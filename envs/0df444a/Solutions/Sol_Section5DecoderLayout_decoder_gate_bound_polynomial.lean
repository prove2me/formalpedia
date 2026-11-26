-- Prove2me | solution 1 for Section5DecoderLayout.decoder_gate_bound_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:59.253839+00:00
-- url     : https://prove2.me/submissions/3a566c9a-283e-41a2-a717-0b04dce4d00f

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
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Mathlib
set_option autoImplicit false
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution (N b f : ℕ) (P : ℝ) (hP : 1 ≤ P)
    (hn : ((N+1:ℕ):ℝ) ≤ P) (hb : ((b+1:ℕ):ℝ) ≤ P) (hf : ((f+2:ℕ):ℝ) ≤ P) :
    (Section5DecoderLayout.decoderGateBound N b f:ℝ) ≤ 500*P^5 := by
  push_cast at hn hb hf
  have hP0 : 0 ≤ P := by linarith
  have hPP : P ≤ P^2 := by nlinarith
  have hP2 : 1 ≤ P^2 := one_le_pow₀ hP
  have hw : 2*((N:ℝ)+1)+b+b+1 ≤ 4*P := by linarith
  have hr : 2*((N:ℝ)+1)+b+b+1+
      (((N:ℝ)+1)*(b+1)+((N:ℝ)+1)*(b+1)) ≤ 6*P^2 := by
    have hnb : ((N:ℝ)+1)*(b+1) ≤ P*P :=
      mul_le_mul hn hb (by positivity) hP0
    nlinarith
  have hs : 16*(2*((N:ℝ)+1)+b+b+1)+6 ≤ 70*P := by linarith
  have hm : 16*(2*((N:ℝ)+1)+b+b+1)+1+7*
      (2*((N:ℝ)+1)+b+b+1+(((N:ℝ)+1)*(b+1)+((N:ℝ)+1)*(b+1))) ≤ 107*P^2 := by
    nlinarith
  have hd : 16*(((N:ℝ)+1)+b+b+1+1)+6 ≤ 54*P := by linarith
  have hrows : ((N:ℝ)+1+((N:ℝ)+1))*(b+1)*(b+1) ≤ 2*P^3 := by
    calc
      _ ≤ (2*P)*P*P := by gcongr; linarith
      _ = _ := by ring
  have hscore : (16*(2*((N:ℝ)+1)+b+b+1)+6)*
      (((N:ℝ)+1+((N:ℝ)+1))*(b+1)*(b+1))*((N:ℝ)+1) ≤ 140*P^5 := by
    calc
      _ ≤ (70*P)*(2*P^3)*P := by gcongr
      _ = _ := by ring
  have hmax : (16*(2*((N:ℝ)+1)+b+b+1)+1+7*
      (2*((N:ℝ)+1)+b+b+1+(((N:ℝ)+1)*(b+1)+((N:ℝ)+1)*(b+1))))*N ≤ 107*P^3 := by
    calc
      _ ≤ (107*P^2)*P := by gcongr; linarith
      _ = _ := by ring
  have hnorm : (16*(((N:ℝ)+1)+b+b+1+1)+6)*
      (((N:ℝ)+1+((N:ℝ)+1))*(b+1)*(b+1)) ≤ 108*P^4 := by
    calc
      _ ≤ (54*P)*(2*P^3) := by gcongr
      _ = _ := by ring
  have hswap : 7*(((N:ℝ)+1)*(b+1)) ≤ 7*P^2 := by
    calc
      _ ≤ 7*(P*P) := by gcongr
      _ = _ := by ring
  have hout : 2*((f:ℝ)+2)*((N:ℝ)+1) ≤ 2*P^2 := by
    calc
      _ ≤ 2*P*P := by gcongr
      _ = _ := by ring
  unfold Section5DecoderLayout.decoderGateBound Section5DecoderLayout.recordWidth Section5DecoderLayout.scoreWidth Section5DecoderLayout.payloadWidth
  push_cast
  nlinarith [pow_le_pow_right₀ hP (show 2 ≤ 5 by omega),
    pow_le_pow_right₀ hP (show 3 ≤ 5 by omega),pow_le_pow_right₀ hP (show 4 ≤ 5 by omega)]
