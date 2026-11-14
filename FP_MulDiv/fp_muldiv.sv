`timescale 1ns / 1ps

module fp_muldiv (
    input  logic        clk,
    input  logic        reset,
    input  logic        in_valid,
    input  logic        div,
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic        out_valid,
    output logic [31:0] result
);

    localparam bit [31:0] CANONICAL_NAN = 32'h7FC0_0000;
    localparam bit [31:0] INF_BASE      = 32'h7F80_0000;
    
    typedef enum logic [3:0] {
        IDLE, UNPACK, SPECIAL_CASES, MUL_EXEC, DIV_EXEC, NORMALIZE, ROUND, PACK
    } state_t;

    state_t state;

    logic        op_div;
    logic [31:0] op_a, op_b;
    logic        sign_res;
    
    logic        a_sign, b_sign;
    logic [7:0]  a_exp, b_exp;
    logic [23:0] a_mant, b_mant; 
    
    logic a_is_nan, a_is_inf, a_is_zero, a_is_sub;
    logic b_is_nan, b_is_inf, b_is_zero, b_is_sub;
    
    logic signed [10:0] calc_exp;
    logic [47:0]        mul_mant;
    logic [49:0]        div_mant;
    logic [23:0]        div_rem;
    logic [5:0]         div_counter;
    
    logic [24:0] norm_mant;      
    logic        guard, round, sticky; 
    logic [31:0] final_result;

    // Combinational rounding logic to easily catch overflow
    logic [24:0] rounded_mant;
    logic        do_round;
    assign do_round = guard && (round || sticky || norm_mant[0]);
    assign rounded_mant = norm_mant + do_round;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
            out_valid <= 1'b0;
            result <= 32'b0;
            op_div <= 1'b0; op_a <= 32'b0; op_b <= 32'b0;
            calc_exp <= 11'b0; mul_mant <= 48'b0; div_mant <= 50'b0;
            div_rem <= 24'b0; div_counter <= 6'b0;
            guard <= 1'b0; round <= 1'b0; sticky <= 1'b0;
            norm_mant <= 25'b0;
        end else begin
            out_valid <= 1'b0; 
            
            case (state)
                IDLE: begin
                    if (in_valid) begin
                        op_a <= a; op_b <= b; op_div <= div;
                        state <= UNPACK;
                    end
                end

                UNPACK: begin
                    a_sign = op_a[31]; b_sign = op_b[31];
                    a_exp  = op_a[30:23]; b_exp  = op_b[30:23];
                    
                    a_is_zero = (a_exp == 8'b0) && (op_a[22:0] == 23'b0);
                    b_is_zero = (b_exp == 8'b0) && (op_b[22:0] == 23'b0);
                    a_is_sub  = (a_exp == 8'b0) && (op_a[22:0] != 23'b0);
                    b_is_sub  = (b_exp == 8'b0) && (op_b[22:0] != 23'b0);
                    a_is_inf  = (a_exp == 8'hFF) && (op_a[22:0] == 23'b0);
                    b_is_inf  = (b_exp == 8'hFF) && (op_b[22:0] == 23'b0);
                    a_is_nan  = (a_exp == 8'hFF) && (op_a[22:0] != 23'b0);
                    b_is_nan  = (b_exp == 8'hFF) && (op_b[22:0] != 23'b0);
                    
                    a_mant = {~a_is_sub & ~a_is_zero, op_a[22:0]};
                    b_mant = {~b_is_sub & ~b_is_zero, op_b[22:0]};
                    
                    sign_res <= a_sign ^ b_sign;
                    state <= SPECIAL_CASES;
                end

                SPECIAL_CASES: begin
                    if (a_is_nan || b_is_nan) begin
                        final_result <= CANONICAL_NAN; state <= PACK;
                    end else if (!op_div) begin 
                        if ((a_is_inf && b_is_zero) || (a_is_zero && b_is_inf)) begin
                            final_result <= CANONICAL_NAN; state <= PACK;
                        end else if (a_is_inf || b_is_inf) begin
                            final_result <= {sign_res, INF_BASE[30:0]}; state <= PACK;
                        end else if (a_is_zero || b_is_zero) begin
                            final_result <= {sign_res, 31'b0}; state <= PACK;
                        end else begin
                            state <= MUL_EXEC;
                        end
                    end else begin 
                        if ((a_is_zero && b_is_zero) || (a_is_inf && b_is_inf)) begin
                            final_result <= CANONICAL_NAN; state <= PACK;
                        end else if (b_is_zero || a_is_inf) begin
                            final_result <= {sign_res, INF_BASE[30:0]}; state <= PACK;
                        end else if (a_is_zero || b_is_inf) begin
                            final_result <= {sign_res, 31'b0}; state <= PACK;
                        end else begin
                            state <= DIV_EXEC;
                            div_rem <= a_mant; div_mant <= 50'b0; div_counter <= 6'd26;
                            calc_exp <= (a_is_sub ? 1 : a_exp) - (b_is_sub ? 1 : b_exp) + 127;
                        end
                    end
                end

                MUL_EXEC: begin
                    mul_mant <= a_mant * b_mant;
                    calc_exp <= (a_is_sub ? 1 : a_exp) + (b_is_sub ? 1 : b_exp) - 127;
                    state <= NORMALIZE;
                end

                DIV_EXEC: begin
                    if (div_counter > 0) begin
                        if (div_rem >= b_mant) begin
                            div_rem <= (div_rem - b_mant) << 1;
                            div_mant <= {div_mant[48:0], 1'b1};
                        end else begin
                            div_rem <= div_rem << 1;
                            div_mant <= {div_mant[48:0], 1'b0};
                        end
                        div_counter <= div_counter - 1'b1;
                    end else begin
                        mul_mant <= {div_mant[25:0], 22'b0}; // Patched: Shifted up to match multiplier format
                        sticky <= (div_rem != 0);   
                        state <= NORMALIZE;
                    end
                end

                NORMALIZE: begin
                    if (mul_mant[47]) begin
                        norm_mant <= {1'b0, mul_mant[47:24]}; 
                        guard <= mul_mant[23]; round <= mul_mant[22];
                        sticky <= sticky | (|mul_mant[21:0]);
                        calc_exp <= calc_exp + 1;
                        state <= ROUND;
                    end else if (mul_mant[46]) begin
                        norm_mant <= {1'b0, mul_mant[46:23]};
                        guard <= mul_mant[22]; round <= mul_mant[21];
                        sticky <= sticky | (|mul_mant[20:0]);
                        state <= ROUND;
                    end else if (mul_mant == 0) begin
                        final_result <= {sign_res, 31'b0};
                        state <= PACK;
                    end else begin
                        mul_mant <= mul_mant << 1;
                        calc_exp <= calc_exp - 1;
                        if (calc_exp <= 1) state <= ROUND;
                    end
                end

                ROUND: begin
                    // Patched: RNTE logic with carry overflow check
                    if (rounded_mant[24]) begin 
                        if (calc_exp + 1 >= 255) final_result <= {sign_res, INF_BASE[30:0]};
                        else final_result <= {sign_res, calc_exp[7:0] + 8'd1, 23'b0};
                    end else begin
                        if (calc_exp >= 255) final_result <= {sign_res, INF_BASE[30:0]};
                        else if (calc_exp <= 0) final_result <= {sign_res, 8'b0, rounded_mant[22:0]};
                        else final_result <= {sign_res, calc_exp[7:0], rounded_mant[22:0]};
                    end
                    state <= PACK;
                end

                PACK: begin
                    result <= final_result; out_valid <= 1'b1; state <= IDLE;     
                end
                
                default: state <= IDLE;
            endcase
        end
    end
endmodule