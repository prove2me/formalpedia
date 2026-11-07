-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_neg_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:18:47.677207+00:00
-- url     : https://prove2.me/submissions/c1e87efc-5945-4a31-94a5-0350e4f93792

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (γ : SL(2,ℤ)) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] (-γ)) =
      ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) := by
  funext z
  rw [ModularForm.SL_slash_apply,ModularForm.SL_slash_apply,ModularGroup.SL_neg_smul]
  simp only [ModularGroup.denom_apply]
  have hd : ((-γ) 1 0 : ℂ)*z+((-γ) 1 1 : ℂ) = -((γ 1 0 : ℂ)*z+(γ 1 1 : ℂ)) := by
    simp
    ring
  rw [hd]
  simp only [zpow_neg,zpow_ofNat,neg_sq]
end QEC.Coding.TannerLiftedProduct
