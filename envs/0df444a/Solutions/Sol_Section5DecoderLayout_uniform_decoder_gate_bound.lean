-- Prove2me | solution 1 for Section5DecoderLayout.uniform_decoder_gate_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:17.157056+00:00
-- url     : https://prove2.me/submissions/6aa5df00-3646-4c9c-9c96-642e013271da

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
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Mathlib
import Theorems.Thm_Section5DecoderLayout_decoder_gate_bound_polynomial
import Theorems.Thm_section5_decoder_parameters_polynomial
set_option autoImplicit false
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (Section5DecoderLayout.decoderGateBound N (section5_decoder_integer_width (N+1) ε)
      (section5_decoder_fraction_bits (N+1) ε):ℝ) ≤ (10:ℝ)^35*(((N+1:ℕ):ℝ)/ε)^15 := by
  obtain ⟨hk,hf,hb⟩ := section5_decoder_parameters_polynomial (N+1) (by omega) ε hε hε'
  let x := ((N+1:ℕ):ℝ)/ε
  have hn1 : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast (show 1 ≤ N+1 by omega)
  have hnle : ((N+1:ℕ):ℝ) ≤ x := by
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hx : 1 ≤ x := hn1.trans hnle
  have hx3 : 1 ≤ x^3 := one_le_pow₀ hx
  have hxx : x ≤ x^3 := by simpa only [pow_one] using pow_le_pow_right₀ hx (show 1 ≤ 3 by omega)
  have h23 : x^2 ≤ x^3 := pow_le_pow_right₀ hx (by omega)
  have hP : 1 ≤ 2000002*x^3 := by linarith
  have hnP : ((N+1:ℕ):ℝ) ≤ 2000002*x^3 := by linarith
  have hbP : ((section5_decoder_integer_width (N+1) ε+1:ℕ):ℝ) ≤ 2000002*x^3 := by
    push_cast
    nlinarith
  have hfP : ((section5_decoder_fraction_bits (N+1) ε+2:ℕ):ℝ) ≤ 2000002*x^3 := by
    push_cast
    nlinarith
  have hbound := Section5DecoderLayout.decoder_gate_bound_polynomial N (section5_decoder_integer_width (N+1) ε)
    (section5_decoder_fraction_bits (N+1) ε) (2000002*x^3) hP hnP hbP hfP
  calc
    _ ≤ 500*(2000002*x^3)^5 := hbound
    _ = (500*2000002^5:ℝ)*x^15 := by ring
    _ ≤ (10:ℝ)^35*x^15 := by gcongr; norm_num
