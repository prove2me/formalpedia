-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_zero_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:19:02.689221+00:00
-- url     : https://prove2.me/submissions/a2372f75-2db6-418d-bb1f-07bdda33d61a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_add_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (γ : SL(2,ℤ)) (hc : γ 1 0=0) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) =
      (fun w : UpperHalfPlane => lpsStandardTheta q w) := by
  have hdet : γ 0 0*γ 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using γ.det_coe
  have hp : Function.Periodic (lpsStandardTheta q) 1 := lpsStandardTheta_add_one q
  have hshift (n : ℤ) (z : ℂ) : lpsStandardTheta q (z+(n:ℂ))=lpsStandardTheta q z := by
    simpa only [mul_one] using hp.int_mul n z
  have hm (z : UpperHalfPlane) : ((γ • z : UpperHalfPlane):ℂ) =
      ((γ 0 0:ℂ)*z+(γ 0 1:ℂ))/((γ 1 0:ℂ)*z+(γ 1 1:ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  funext z
  rw [ModularForm.SL_slash_apply]
  change lpsStandardTheta q ((γ • z : UpperHalfPlane):ℂ) *
    (((γ 1 0:ℂ)*z+(γ 1 1:ℂ)) ^ (-(2:ℤ))) = lpsStandardTheta q z
  rw [hm]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · simpa [hc,ha,hd] using hshift (γ 0 1) z
  · simpa [hc,ha,hd,sub_eq_add_neg,div_neg,neg_add,add_comm] using hshift (-γ 0 1) z
end QEC.Coding.TannerLiftedProduct
