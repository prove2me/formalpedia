-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:45:08.1892+00:00
-- url     : https://prove2.me/submissions/051922ab-28aa-40a3-8a0a-87eb3d83d497

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_S_raw
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
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2 : ℤ)] ModularGroup.S) z =
      -(32*(q:ℂ)^3)⁻¹ * jacobiTheta ((z:ℂ)/2) *
        jacobiTheta ((z:ℂ)/(8*(q:ℂ)^2))^3 := by
  have qn : (q:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have zn : (z:ℂ) ≠ 0 := z.ne_zero
  rw [SlashInvariantForm.slash_S_apply]
  simp only
  rw [show (-(z:ℂ))⁻¹ = -1/(z:ℂ) by field_simp,
    lpsStandardTheta_S_raw q hq (z:ℂ) z.im_pos]
  simp only [zpow_neg,zpow_ofNat]
  field_simp
end QEC.Coding.TannerLiftedProduct
