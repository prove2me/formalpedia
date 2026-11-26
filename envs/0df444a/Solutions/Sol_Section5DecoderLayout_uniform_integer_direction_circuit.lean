-- Prove2me | solution 1 for Section5DecoderLayout.uniform_integer_direction_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:58:32.095738+00:00
-- url     : https://prove2.me/submissions/9f637ff0-b22f-4583-9148-2759b785cbdd

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Definitions.Def_Section5Verified_Section5IntegerDirectionSpec
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
import Theorems.Thm_Section5DecoderLayout_integer_matrix_direction_spec
import Theorems.Thm_Section5DecoderLayout_uniform_decoder_gate_bound
import Theorems.Thm_section5_decoder_parameters_sufficient
import Theorems.Thm_section5_decoder_power_gate_bound
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    let K := section5_decoder_iterations (N+1) ε
    let f := section5_decoder_fraction_bits (N+1) ε
    let b := section5_decoder_integer_width (N+1) ε
    ∃ circ : Circuit gatesRev (Section5DecoderLayout.width N K b f),
      (circ.size:ℝ) ≤ (10:ℝ)^36*(((N+1:ℕ):ℝ)/ε)^15 ∧
      Section5DecoderLayout.DirectionSpec N K b f f ε circ := by
  obtain ⟨hiter,hbits,hn,hf,hfit,hwidth⟩ := section5_decoder_parameters_sufficient (N+1) ε hε
  obtain ⟨circ,hsize,hact⟩ := Section5DecoderLayout.integer_matrix_direction_spec N
    (section5_decoder_iterations (N+1) ε) (section5_decoder_integer_width (N+1) ε)
    (section5_decoder_fraction_bits (N+1) ε) (section5_decoder_fraction_bits (N+1) ε)
    (section5_binary_precision ((N+1:ℕ):ℝ)) hn hwidth hf hfit ε hε hε' hiter hbits
  refine ⟨circ,?_,?_⟩
  · have hsize' : (circ.size:ℝ) ≤
        ((88*(N+1)^3*(section5_decoder_integer_width (N+1) ε+1)^3)*
          section5_decoder_iterations (N+1) ε:ℕ)+
        (Section5DecoderLayout.decoderGateBound N (section5_decoder_integer_width (N+1) ε)
          (section5_decoder_fraction_bits (N+1) ε):ℝ) := by
      have hh : (circ.size:ℝ) ≤
          (((88*(N+1)^3*(section5_decoder_integer_width (N+1) ε+1)^3)*
            section5_decoder_iterations (N+1) ε+
            Section5DecoderLayout.decoderGateBound N (section5_decoder_integer_width (N+1) ε)
              (section5_decoder_fraction_bits (N+1) ε):ℕ):ℝ) := Nat.cast_le.mpr hsize
      rw [Nat.cast_add] at hh
      exact hh
    have hp := section5_decoder_power_gate_bound (N+1) (by omega) ε hε hε'
    have hd := Section5DecoderLayout.uniform_decoder_gate_bound N ε hε hε'
    let x := ((N+1:ℕ):ℝ)/ε
    have hn1 : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast (show 1 ≤ N+1 by omega)
    have hnle : ((N+1:ℕ):ℝ) ≤ x := by
      apply (le_div_iff₀ hε).mpr
      exact (mul_le_mul_of_nonneg_left hε'.le (by positivity)).trans_eq (mul_one _)
    have hx : 1 ≤ x := hn1.trans hnle
    have hpow : x^13 ≤ x^15 := pow_le_pow_right₀ hx (by omega)
    calc
      _ ≤ (10:ℝ)^25*x^13+(10:ℝ)^35*x^15 := hsize'.trans (add_le_add hp hd)
      _ ≤ (10:ℝ)^25*x^15+(10:ℝ)^35*x^15 :=
        add_le_add (mul_le_mul_of_nonneg_left hpow (by norm_num)) le_rfl
      _ = ((10:ℝ)^25+(10:ℝ)^35)*x^15 := by ring
      _ ≤ (10:ℝ)^36*x^15 := mul_le_mul_of_nonneg_right (by norm_num)
        (pow_nonneg (le_trans (by norm_num) hx) 15)
  · exact hact
