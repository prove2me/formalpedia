-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_not_dvd_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:58:30.49019+00:00
-- url     : https://prove2.me/submissions/8bb1123a-d7b2-40c5-b60f-3a76b8e714ed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspGcd_of_not_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_fin_sum_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_gcd_tendsto
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (hC : ¬(q:ℤ)∣γ 1 0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 0) := by
  have ht := lpsQuadraticE2Twist_cusp_gcd_tendsto q γ
  have hs : (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2))=
      (1/(q:ℂ)^2)*(∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hz : r=0
    · subst r
      simp only [Fin.val_zero,Nat.cast_zero,MulChar.map_zero,zero_mul,mul_zero]
    · rw [lpsQuadraticEisensteinCuspGcd_of_not_dvd q γ r hz hC]
      simp only [Nat.cast_one,one_pow]
      ring
  rw [hs,lpsQuadraticE2Character_fin_sum_zero q hq2,mul_zero,mul_zero] at ht
  exact ht
end QEC.Coding.TannerLiftedProduct
