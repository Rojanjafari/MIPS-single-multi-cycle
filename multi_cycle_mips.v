
`timescale 1ns/100ps

   `define ADD  3'b000
   `define SUB  3'b001
   `define SLT  3'b010
   `define SLTU 3'b011
   `define AND  3'b100
   `define XOR  3'b101
   `define OR   3'b110
   `define NOR  3'b111

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR;

   // Data Path Control Lines, don't forget, regs are not always register !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;

   // Memory Ports Bindings
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Line
   reg [2:0] aluOp;
   reg [2:0] aluSelB;
   reg [1:0] aluSelA;
   reg SgnExt, IorD, Branch, move, start_mult;
   reg [1:0] MemtoReg, RegDst;
   // Wiring
   wire aluZero, ready_mult;
   wire [31:0] aluResult, rfRD1, rfRD2, high, low;


   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt )
         PC <= #0.1 aluResult;

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;

   end

   // Register File
   reg [31:0] WD_rf;
   always @(*)
   case (MemtoReg)
      2'b00: WD_rf = aluResult; 
      2'b01: WD_rf = MDR;
      2'b10: WD_rf = {IR[15:0], 16'h0000};
   endcase

   reg [4:0] WR_rf;
   always @(*)
   case (RegDst)
      2'b00: WR_rf = IR[20:16]; 
      2'b01: WR_rf = IR[15:11];
      2'b10: WR_rf = 5'b11111;
   endcase

   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR( WR_rf ),
      .WD( WD_rf )
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   reg [31:0] aluA;
   always @(*)
   case (aluSelA)
      2'b00: aluA = PC;
      2'b01: aluA = A;
      2'b10: aluA = 32'h00000;
      2'b11: aluA = IR[25:21];
   endcase

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      3'b000: aluB = B;
      3'b001: aluB = 32'h4;
      3'b010: aluB = SZout;
      3'b011: aluB = SZout << 2;
      3'b100: aluB = {PC[31:28], IR[25:0] << 2};
      3'b101: aluB = 32'h0;
      3'b111: aluB = move ? high : low;
   endcase 

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );

   multu mult(
      .clk( clk ),
      .start( start_mult ),
      .A( aluA ),
      .B( aluB ),
      .hi( high ),
      .lo( low ),
      .ready( ready_mult )
   );

   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 5, EX_ALU_I = 6,  
      EX_MULTU_1 = 7, EX_MULTU_2 = 8, 
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_MF = 16,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26,
      EX_LUI = 17,
      EX_J = 18,
      EX_JAL_1 = 19, EX_JAL_2 = 20,
      EX_JR = 27, EX_JR_1 = 28,
      EX_JALR_1 = 29, EX_JALR_2 = 30, EX_JALR_3 = 31;
      

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;
      move = 'bx; Branch = 'bx;

      PCwrt = 0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 2'b00;
            aluSelB = 3'b001;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            SgnExt = 1;
            aluSelA = 2'b00;
            aluSelB = 3'b011;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001:
                        case( IR[2:0] )
                           3'b000: nxt_state = EX_JR;
                           3'b001: nxt_state = EX_JALR_1; 
                        endcase

                     3'b010: nxt_state = EX_MF;
                     3'b011: nxt_state = EX_MULTU_1;
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110:             // xori
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b001_111:
                  nxt_state = EX_LUI;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;
                  

               6'b000_010: //jump
                  nxt_state = EX_J; 

               6'b000_011: //jal
                  nxt_state = EX_JAL_1;


               // rest of instructiones should be decoded here

            endcase
         end

         EX_ALU_R: begin
            aluSelA = 2'b01;
            aluSelB = 3'b000;
            case(IR[5:3])
               3'b100:
                  case(IR[2:0])
                     3'b000: aluOp = `ADD; //add
                     3'b001: aluOp = `ADD; //addu
                     3'b010: aluOp = `SUB; //sub
                     3'b011: aluOp = `SUB; //subu
                     3'b100: aluOp = `AND; //and
                     3'b101: aluOp = `OR; //or
                     3'b110: aluOp = `XOR; //xor
                     3'b111: aluOp = `NOR;
                  endcase
               3'b101:
                  case(IR[2:0])
                     3'b000: ; 
                     3'b001: ; 
                     3'b010: aluOp = `SLT; //slt
                     3'b011: aluOp = `SLTU; //sltu
                     3'b100: ;
                     3'b101: ; 
                     3'b110: ; 
                     3'b111: ;
                  endcase
            endcase 
            RFwrt = 1;
            RegDst = 2'b01;
            MemtoReg = 2'b00;
            PrepareFetch;
         end

         //mfhi & mflo
         EX_MF: begin
            aluSelA = 2'b10; 
            aluSelB = 3'b111; 
            aluOp = `ADD;
            case(IR[2:0])
               3'b000: move = 1; //mfhi
               3'b010: move = 0; //mflo
            endcase
            RegDst = 2'b01;
            MemtoReg = 2'b00;
            RFwrt = 1;
            PrepareFetch;
         end

    
         //multu
         EX_MULTU_1: begin
            start_mult = 1;
            aluSelA = 2'b01;
            aluSelB = 3'b000;
            nxt_state = EX_MULTU_2;
         end

         EX_MULTU_2: begin
            start_mult = 0;
            if(ready_mult == 0)
               nxt_state = EX_MULTU_2;
            else
               PrepareFetch;
         end

         EX_ALU_I: begin
            aluSelA = 2'b01;
            case(IR[31:26])
               6'b001_000: begin // addi
                  SgnExt = 1;
                  aluSelB = 3'b010;
                  aluOp = `ADD; 
               end
               6'b001_001: begin // addiu
                  SgnExt = 1;
                  aluSelB = 3'b010;
                  aluOp = `ADD; 
               end
               6'b001_010: begin // slti
                  SgnExt = 1;
                  aluSelB = 3'b010;
                  aluOp = `SLT; 
               end
               6'b001_011: begin // sltiu
                  SgnExt = 1;
                  aluSelB = 3'b010;
                  aluOp = `SLTU; 
               end
               6'b001_100: begin // andi
                  SgnExt = 0;
                  aluSelB = 3'b010;
                  aluOp = `AND; 
               end
               6'b001_101: begin // ori
                  SgnExt = 0;
                  aluSelB = 3'b010;
                  aluOp = `OR; 
               end
               6'b001_110: begin // xori
                  SgnExt = 0;
                  aluSelB = 3'b010;
                  aluOp = `XOR; 
               end
            endcase

            RFwrt = 1; 
            RegDst = 2'b00;
            MemtoReg = 2'b00;
            PrepareFetch;
         end

         //lw
         EX_LW_1: begin
            IorD = 1;
            MARwrt = 1;
            setMRE = 1;
            aluSelA = 2'b01;
            SgnExt = 1;
            aluSelB = 3'b010;
            aluOp = `ADD;
            nxt_state = EX_LW_2;
         end

         EX_LW_2:
            nxt_state = EX_LW_3;

         EX_LW_3:
            nxt_state = EX_LW_4;

         EX_LW_4: begin
            clrMRE = 1;
            MDRwrt = 1;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            MemtoReg = 2'b01;
            RFwrt = 1;
            RegDst = 2'b00;
            
           PrepareFetch;
         end

         //lui
         EX_LUI: begin
            IorD = 1;
            MARwrt = 1;
            setMRE = 1;
            aluSelA = 2'b01;
            SgnExt = 1;
            aluSelB = 3'b110;
            aluOp = `ADD;
            MemtoReg = 2'b10;
            RFwrt = 1;
            RegDst = 2'b00;
            PrepareFetch;
         end
         
         //sw
         EX_SW_1: begin
            IorD = 1;
            MARwrt = 1;
            setMWE = 1;
            aluSelA = 2'b01;
            SgnExt = 1;
            aluSelB = 3'b010;
            aluOp = `ADD;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            clrMWE = 1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3: 
            PrepareFetch;

         //branch
         EX_BRA_1: begin
            PCwrt = 0;
            aluSelA = 2'b01;
            aluSelB = 3'b000;
            aluOp = `SUB;
            Branch = 1;
            case(IR[31:26])
               //beq
               6'b000_100: begin
                  if(aluZero == 1)
                     nxt_state = EX_BRA_2;
                  else
                     PrepareFetch;
               end
               //bne
               6'b000_101: begin
                  if(aluZero == 0)
                     nxt_state = EX_BRA_2;
                  else
                      PrepareFetch;
               end
            endcase
         end

         EX_BRA_2: begin
            MARwrt = 1;
            IorD = 1;
            PCwrt = 1;
            aluSelA = 2'b00;
            SgnExt = 1;
            aluSelB = 3'b011;
            aluOp = `ADD;
            setMRE = 1;
            nxt_state = FETCH1;
         end

         //jump
         EX_J: begin
            MARwrt = 1;
            IorD = 1;
            PCwrt = 1;
            aluSelA = 2'b10;
            aluSelB = 3'b100;
            aluOp = `ADD;
            setMRE = 1;
            nxt_state = FETCH1;
         end
         
         //jal
         EX_JAL_1: begin
            aluSelA = 2'b00;
            aluSelB = 3'b101;
            aluOp = `ADD;
            RegDst = 2'b10;
            MemtoReg = 2'b00;
            RFwrt = 1;
            nxt_state = EX_JAL_2;
         end

         EX_JAL_2: begin
            MARwrt = 1;
            IorD = 1;
            PCwrt = 1;
            aluSelA = 2'b10;
            aluSelB = 3'b100;
            aluOp = `ADD;
            setMRE = 1;
            nxt_state = FETCH1;
         end

         //jr
         EX_JR: begin
            aluSelA = 2'b01;
            aluSelB = 3'b101;
            aluOp = `ADD;
            MARwrt = 1;
            IorD = 1;
            PCwrt = 1;
            setMRE = 1;
            nxt_state = EX_JR_1;
         end
         
         EX_JR_1: begin
            PrepareFetch;
         end

         //jalr
         EX_JALR_1: begin
            aluSelA = 2'b00;
            aluSelB = 3'b101;
            aluOp = `ADD;
            RegDst = 2'b10;
            MemtoReg = 2'b00;
            RFwrt = 1;
            nxt_state = EX_JALR_2;
         end

         EX_JALR_2: begin
            MARwrt = 1;
            IorD = 1;
            PCwrt = 1;
            aluSelA = 2'b01;
            aluSelB = 3'b101;
            aluOp = `ADD;
            setMRE = 1;
            nxt_state = EX_JALR_3;
         end

         EX_JALR_3:
            PrepareFetch;


      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [2:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;

   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================

module multu(
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output [31:0] lo,
   output [31:0] hi,
   output ready
);


   reg [31:0] Multiplicand ;
   reg [5:0]  counter;
   reg [63:0] Product;

   wire product_write_enable = Product[0];
   wire [31:0] mux = Product[0] ? Multiplicand : 32'h00000000;
   wire [32:0] adder_output = mux + Product[63:32];

   assign ready = counter[5];


   always @ (posedge clk)

      if(start) begin
         counter <= 5'h00 ;
         Multiplicand <= A ;
         Product <= {32'h00000000, B} ;
      end

      else if(! ready) begin
            counter <= counter + 1;
            Product <= Product >> 1;

         if(product_write_enable) begin
            Product[63:31] <= adder_output;
         end   
         
      end   

      assign hi = Product[63:32];
      assign lo = Product[31:0];

endmodule