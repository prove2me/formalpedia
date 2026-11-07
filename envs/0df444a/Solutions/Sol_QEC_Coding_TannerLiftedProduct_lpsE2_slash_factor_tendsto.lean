-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2_slash_factor_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:04:57.096179+00:00
-- url     : https://prove2.me/submissions/d45166aa-17c8-41ce-835a-1379adcc1869

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_tendsto_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlash_tendsto_upperTriangular
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
theorem _root_.solution (δ : SL(2,ℤ)) (h : GL (Fin 2) ℝ)
    (hc : h 1 0=0) (hd : 0<h.det.val) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ δ*h))
      UpperHalfPlane.atImInfty (𝓝 ((h.det.val:ℂ)*(h 1 1:ℂ)^(-(2:ℤ)))) := by
  rw [SlashAction.slash_mul]
  have hf : Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ δ)
      UpperHalfPlane.atImInfty (𝓝 1) := by
    simpa [Matrix.SpecialLinearGroup.mapGL,← ModularForm.SL_slash] using
      lpsE2_slash_tendsto_one δ
  simpa only [one_mul] using lpsWeightTwoSlash_tendsto_upperTriangular _ 1 hf h hc hd
end QEC.Coding.TannerLiftedProduct
