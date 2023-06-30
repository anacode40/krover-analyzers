/*
ANALYSIS SCENARIO : Detecting an OOB write in the TIPC module and its analysis

Following APIs privided by KRover are used by the analyst
--Obtain runtime CPU state through VM state
	struct pt_regs <<= m_vm->getPTRegs();
	struct pt_regs in KRover has the same definition as that of the Linux kernel
	
--Declare new memory symbols
	declareSymbolicObject(address, size, isSigned, hasSeed, seed_value, symbol_name)

--Declare new register symbols
	declareSymbolicRegister(register_index, size, isSigned, hasSeed, seed_value, symbol_name)

--Dispatch for symbolic execution
	m_FattCtrl->processFunc(starting_instruction_address)
	
--Read a register from KRover's symbolic state
    m_VM->readRegister(RegValue V);
	Allways already synced with runtime CPU state
	Reading a register from KRover's symbolic state exposes the symbolic attributes,
	such as the current symbolic expression if the register is symbolic
	
--Write a register in KRover's symbolic state
	m_VM->writeRegister (RegValue V) ;
	
*/

unsigned long kmalloc_function_address    = kernel_symbol_lookup("kmalloc");
unsigned long memcpy_instruction_address  = kernel_symbol_lookup("memcpy_erms") + 0x6;

/*This analyzer procedure executes prior to the start of dynamic symbolic execution*/
bool beginAnalystMode()
{
    struct pt_regs  *m_regs;
    unsigned long   skb;
    unsigned long   ptr_to_skb_data;
    uint8_t         *data;
    uint8_t         *data_start;

    unsigned long   sym_address, offset;
    string          symbol_name, s_base;
    uint8_t         offset;

    /*
	starting analysis at tipc_udp_recv :function top
	This is the point of the target kernel thread export to KRover(onsite environment)
	*/
    m_regs          = m_VM->getPTRegs();
    /*
    perform dynamic introspection, traverse kernel data structures to find the address of the tipc packet contents
    */
    skb             = m_regs->rbx;
    ptr_to_skb_data = skb + 0xc8;
    data_start      = *((uint8_t**)ptr_to_skb_data);
    data            = (uint8_t *)((unsigned long)data_start + 0x8);    //skip first 8 bytes, UDP header
    //data points to the TIPC pachet header

    /*
    before the dynamic symbolic analysis begin symbolize the kernel memory block(124 bits as per the poc) holding the tipc packet
    */
    offset          = 0;
    s_base          = "packet_bytes_";
    sym_address     = (unsigned long)data;
    symbol_name     = s_base + to_string(offset);

    declareSymbolicObject(sym_address, 4, 0, 1, *(unsigned long*)sym_address, symbol_name); //symbolize  tipc hdr 
    offset          += 4;
    while(offset <= 116){
        sym_address = (unsigned long)data + offset;
        symbol_name = s_base + to_string(offset);
        declareSymbolicObject(sym_address, 8, 0, 1, *(unsigned long*)sym_address, symbol_name); //symbolize  tipc hdr 
        offset      += 8;
    }

    //dispatch for Fat-Control
    return m_FattCtrl->processFunc(m_regs->rip);
}

/*
this analyer procedure executes after each instruction to detect the events under interest to complete the analysis task
and detect the potential overfllow
*/
bool analyzeExecution(){

        unsigned long concrete_reg_val;
        bool res;

        if(in->getCategory() == c_CallInsn){
            /*
            After a call instructions has been executed,
            analyzer obtains the return address for call instructions from stack top as the analyzer has access to CPU state
            */
            caller_adr_aft_ret = *((unsigned long*) (m_regs->rsp));
            //do not return here
        }

        /*analyzer gets the kmalloc function address via kernel symbol table*/
        if(m_regs->rip == kmalloc_function_address) //next instruction is kmalloc
        {
            kmalloc_ret_adr = caller_adr_aft_ret;
            kmalloc_invoked = true;

            std::cout << "\nkmalloc returns to : " << kmalloc_ret_adr << std::endl;

            /*
            As per x64 ABI %rdi holds  first function argument, kmalloc size
            */
            RegValue V{(uint)x86_64::rdi, 0x8} ;
            res = m_VM->readRegister(V);
            assert(res);
            unsigned long r_rdi = V.u64;

            /*
            When the entire TIPC packet contents have been symbolized &
            if the kmalloc size is derived from packet contents,
            kmalloc size will be symbolic
            */
            if(V.bsym)
            {
                std::cout << "smbolic sykmalloc size : Expression : ";
                V.expr->print();
                std::cout << std::endl;

                /*
                Our requrement was to see which part of the packet contents is used to derive the kmalloc size.
                Hence, in this analysis job, no point of keeping the kmalloc size symbolic beyond this point.
                It is not possible to issue kmalloc with a symbolic size. 
                Issuing the kmalloc with a concrete size.
                call z3 API to obtain a concrete kmalloc size based on the original seed values of the symbolic size.
                */
                concrete_reg_val = m_EFlagsMgr->ConcretizeExpression(V.expr); 
                std::cout << "concretized val : " << std::hex << concrete_reg_val << std::endl;

                V.bsym = false ;
                V.u64 = concrete_reg_val ;
                /*write the concrete value on to the register, rdi, concretize*/
                m_VM->writeRegister (V) ;
            }
            else
            {
                std::cout << "rdi is not a symbol, value: 0x" << std::hex << r_rdi << std::endl;
            }

            return true;
        }
        /*detect returns form kmalloc here*/
        if(kmalloc_invoked && (m_regs->rip == kmalloc_ret_adr))
        {
            kmalloc_invoked = false;

            /*as per x64 ABI %rax holds the function return value*/
            RegValue V{(uint)x86_64::rax, 0x8} ;
            res = m_VM->readRegister(V);
            assert(res);
            unsigned long r_rax = V.u64;
            if(V.bsym)
            {
                std::cout << "rax is a symbol" << std::endl;
                //path not possible
                assert(0);
            }
            else
            {
                /*
                To detect future accesss to the kmalloced buffer,
                Option 1: To detect all future memory accesses as an offset to the kmalloced buffer start address
                symbolize the buffer address.
                Option 2: Since we already know the kmalloced buffer size,
                symbolixe the entire buffer content.
                Both options are possible at this moment, For this analysis task, we select the Option 1.
                */
                std::cout << "kmalloced buf adr, rax:" << r_rax << " ,Tagging the kmalloced buffer by symbolizing rax" << std::endl;
                string symbol_name = "heap_buffer";
                /*runtime/dynamic symbolization; symbolizing the %rax register*/
                m_VM->createSYRegObject((uint)x86_64::rax, 8, 0, 1, r_rax, symbol_name);
            }

            return true;
        }
        /*inspect all memcpy() invocations to detect potential buffer overflows through memcpy()*/
        if(m_regs->rip == memcpy_instruction_address) 
        {
            /*
            Linux fast memcpy() implementation is as follows
            rep movsb
            rdi <- memcpy destination
            rsi <- memcpy source
            rcx <- memcpy length, repetion count for movsb instruction above
            */

            std::cout << "\nInspecting memcpy size" << std::endl;
            RegValue V{(uint)x86_64::rcx, 0x8} ;
            res = m_VM->readRegister(V);
            assert(res);
            unsigned long r_rdx = V.u64;
            if(V.bsym)
            {
                //memcpy size is symbolic and user determined, hence a potential OOB wwrite
                std::cout << "Potential OOB write detected, memcpy size is symbolic : Expression : ";
                V.expr->print();
                std::cout << std::endl;
            }
            else
            {
                std::cout << "rcx is not a symbol, value: 0x" << std::hex << r_rdx << std::endl;
            }

            std::cout << "\nInspecting memcpy source address" << std::endl;
            RegValue V1{(uint)x86_64::rsi, 0x8} ;
            res = m_VM->readRegister(V1);
            assert(res);
            unsigned long r_rsi = V1.u64;
            if(V1.bsym)
            {
                std::cout << "memcpy src address, rsi is symbolic: Expression : ";
                V1.expr->print();
                std::cout << std::endl;
            }
            else
            {
                std::cout << "memcpy src address, rsi : 0x" << std::hex << r_rsi << std::endl;
            }

            std::cout << "\nInspecting memcpy destinaiton address" << std::endl;
            RegValue V2{(uint)x86_64::rdi, 0x8} ;
            res = m_VM->readRegister(V2);
            assert(res);
            unsigned long r_rdi = V2.u64;
            if(V2.bsym)
            {
                std::cout << "memcpy destination address, rdi is symbolic: Expression : ";
                V2.expr->print();
                std::cout << std::endl;
            }
            else
            {
                std::cout << "memcpy destination address, rdi : 0x" << std::hex << r_rdi << std::endl;
            }

            
            return true;
        }

        return true;
}