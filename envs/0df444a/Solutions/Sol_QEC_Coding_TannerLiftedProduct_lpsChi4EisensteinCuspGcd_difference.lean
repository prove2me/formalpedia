-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspGcd_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:52:19.339197+00:00
-- url     : https://prove2.me/submissions/9e4166c2-8a95-49c6-b5e4-c653097938bc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (A C : ℤ)
    (hp : ¬(2∣A ∧ 2∣C)) :
    (((Int.gcd (4*A+C) 16:ℕ):ℂ)^2-((Int.gcd (4*A+3*C) 16:ℕ):ℂ)^2)=
      if C%8=4 then -192*lpsChi4E2Character ((A*(C/4):ℤ):ZMod 4) else 0 := by
  have h1 : Int.gcd (4*A+C) 16=Int.gcd (4*(A%4)+C%16) 16 := by
    rw [←Int.gcd_emod (4*A+C) 16,←Int.gcd_emod (4*(A%4)+C%16) 16]
    congr 1
    omega
  have h3 : Int.gcd (4*A+3*C) 16=Int.gcd (4*(A%4)+3*(C%16)) 16 := by
    rw [←Int.gcd_emod (4*A+3*C) 16,←Int.gcd_emod (4*(A%4)+3*(C%16)) 16]
    congr 1
    omega
  have hdiv : (C/4)%4=(C%16)/4 := by omega
  have hcast : ((A*(C/4):ℤ):ZMod 4)=((A%4)*((C%16)/4):ℤ) := by
    push_cast
    rw [←ZMod.intCast_mod A 4,←ZMod.intCast_mod (C/4) 4]
    norm_num only [Nat.cast_ofNat]
    rw [hdiv]
  have hp' : ¬((A%4)%2=0 ∧ (C%16)%2=0) := by
    simpa only [Int.emod_emod_of_dvd A (by norm_num : (2:ℤ)∣4),
      Int.emod_emod_of_dvd C (by norm_num : (2:ℤ)∣16),Int.dvd_iff_emod_eq_zero] using hp
  have h8 : C%8=(C%16)%8 := by omega
  rw [h1,h3,hcast,h8]
  have ha0 : 0≤A%4 := Int.emod_nonneg _ (by norm_num)
  have ha4 : A%4<4 := Int.emod_lt_of_pos _ (by norm_num)
  have hc0 : 0≤C%16 := Int.emod_nonneg _ (by norm_num)
  have hc16 : C%16<16 := Int.emod_lt_of_pos _ (by norm_num)
  generalize A%4=a at *
  generalize C%16=c at *
  interval_cases a <;> interval_cases c
  all_goals norm_num at hp'
  all_goals norm_num [lpsChi4E2Character_apply,ZMod.χ₄_apply]
end QEC.Coding.TannerLiftedProduct
