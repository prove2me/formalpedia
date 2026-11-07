-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_square_dvd_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:01:07.884707+00:00
-- url     : https://prove2.me/submissions/4be528ad-13e7-4ffe-ba40-b00a1def695c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_fin_sum_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspGcd_weighted_of_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_unit_of_prime_dvd
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
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (hD : (D:ZMod q)=0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 0) := by
  have hCd : (q:ℤ)∣γ 1 0 := ⟨D,hC⟩
  have hA := lpsSL2Z_firstColumn_unit_of_prime_dvd q γ hCd
  have ht := lpsQuadraticE2Twist_cusp_gcd_tendsto q γ
  have he : (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2))=
      (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)) := by
    simp_rw [lpsQuadraticEisensteinCuspGcd_weighted_of_dvd q γ D hC]
    simp only [hD,mul_zero,add_zero,if_neg hA,mul_one]
  rw [he,lpsQuadraticE2Character_fin_sum_zero q hq2,mul_zero] at ht
  exact ht
end QEC.Coding.TannerLiftedProduct
