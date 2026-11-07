-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2ShiftAtPrimeCusp_tendsto_of_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:06:13.208101+00:00
-- url     : https://prove2.me/submissions/9a7ff88c-25cf-4ba7-96f9-06e157acd047

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_factor_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2CuspFactor
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
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [NeZero q] (r : ℤ)
    (g : ℝ) (hg : g≠0) (δ : SL(2,ℤ))
    (ha : (δ 0 0:ℝ)*g=(r:ℝ)+1) (hc : (δ 1 0:ℝ)*g=(q:ℝ)) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2 (((r:ℝ)/(q:ℝ)) +ᵥ z))
      ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) UpperHalfPlane.atImInfty (𝓝 ((g:ℂ)^2)) := by
  let b : ℝ := (δ 1 1:ℝ)*(r:ℝ)/(q:ℝ)-(δ 0 1:ℝ)
  let h := Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DiagonalTranslation g b hg)
  have hh10 : h 1 0=0 := by
    change (algebraMap ℝ ℝ) 0=0
    exact map_zero _
  have hh11 : h 1 1=g⁻¹ := by
    change (algebraMap ℝ ℝ) (g⁻¹)=g⁻¹
    rfl
  have hdet : h.det.val=1 := by simp [h]
  have hp : 0<h.det.val := by rw [hdet];norm_num
  have hl := lpsE2_slash_factor_tendsto δ h hh10 hp
  rw [ModularForm.SL_slash]
  change Tendsto ((fun z : ℍ => EisensteinSeries.E2 (((r:ℝ)/(q:ℝ)) +ᵥ z))
    ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2PrimeCuspMatrix q))
      UpperHalfPlane.atImInfty (𝓝 ((g:ℂ)^2))
  rw [← lpsE2RealTranslation_slash,← SlashAction.slash_mul,
    lpsE2CuspFactor q r g hg δ ha hc]
  simpa only [hdet,hh11,Complex.ofReal_one,one_mul,Complex.ofReal_inv,zpow_neg,zpow_ofNat,
    inv_pow,inv_inv] using hl
end QEC.Coding.TannerLiftedProduct
