-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRealShiftInverse_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:00:58.302487+00:00
-- url     : https://prove2.me/submissions/a3dba724-9d1b-4837-883e-c6ebc01870b8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
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
theorem _root_.solution (r : ℝ) :
    Tendsto (fun z : ℍ => ((z:ℂ)+(r:ℂ))⁻¹) UpperHalfPlane.atImInfty (𝓝 0) := by
  have hi : Tendsto (fun z : ℍ => z.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
  have hn : Tendsto (fun z : ℍ => ‖(z:ℂ)+(r:ℂ)‖) UpperHalfPlane.atImInfty atTop :=
    tendsto_atTop_mono (fun z => by simpa using Complex.im_le_norm ((z:ℂ)+(r:ℂ))) hi
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_inv,Function.comp_def] using tendsto_inv_atTop_zero.comp hn
end QEC.Coding.TannerLiftedProduct
