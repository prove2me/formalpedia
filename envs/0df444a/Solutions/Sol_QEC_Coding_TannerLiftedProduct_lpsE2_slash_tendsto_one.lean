-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2_slash_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:03:18.725619+00:00
-- url     : https://prove2.me/submissions/69910589-51ea-4692-891c-f5edd660b521

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_tendsto_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Defect_tendsto_zero
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
theorem _root_.solution (γ : SL(2,ℤ)) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 1) := by
  rw [EisensteinSeries.E2_slash_action]
  change Tendsto (fun z : ℍ => EisensteinSeries.E2 z -
    (1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z) UpperHalfPlane.atImInfty (𝓝 1)
  simpa only [smul_zero,sub_zero,smul_eq_mul,mul_zero] using lpsE2_tendsto_one.sub
    ((lpsE2Defect_tendsto_zero γ).const_smul (1/(2*riemannZeta 2)))
end QEC.Coding.TannerLiftedProduct
