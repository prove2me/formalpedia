-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinQuadraticWeight_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:40:35.234937+00:00
-- url     : https://prove2.me/submissions/78630860-677f-47bd-bc0b-8e0a4ae991df

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsStandardThetaModularForm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) :
    lpsThetaEisensteinQuadraticWeight q a*lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)/
      ((2^a.val:ℕ):ℂ)^2= -lpsThetaEisensteinTwoWeight a/((2^a.val:ℕ):ℂ) := by
  have hn : (2:ZMod q)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    exact hq2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).mp hd)
  have hs : (lpsQuadraticE2Character q (2:ZMod q))^2=1 := by
    simpa only [map_pow] using lpsQuadraticE2Character_square q (2:ZMod q) hn
  have h4 : (lpsQuadraticE2Character q (2:ZMod q))^4=1 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,hs,one_pow]
  have h16 : (lpsQuadraticE2Character q (2:ZMod q))^16=1 := by
    rw [show (16:ℕ)=2*8 by decide,pow_mul,hs,one_pow]
  rw [Nat.cast_pow,map_pow]
  fin_cases a <;> norm_num [lpsThetaEisensteinQuadraticWeight,lpsThetaEisensteinTwoWeight,hs,h4,h16]
  all_goals linear_combination 3*hs
end QEC.Coding.TannerLiftedProduct
