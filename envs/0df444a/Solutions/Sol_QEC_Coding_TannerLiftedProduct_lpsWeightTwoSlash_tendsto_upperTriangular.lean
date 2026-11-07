-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlash_tendsto_upperTriangular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:19.214495+00:00
-- url     : https://prove2.me/submissions/ef665b05-8feb-42da-ae67-ab2b0f8fc828

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
theorem _root_.solution (f : ℍ→ℂ) (L : ℂ)
    (hf : Tendsto f UpperHalfPlane.atImInfty (𝓝 L)) (g : GL (Fin 2) ℝ)
    (hc : g 1 0=0) (hd : 0<g.det.val) :
    Tendsto (f ∣[(2:ℤ)] g) UpperHalfPlane.atImInfty
      (𝓝 (L*(g.det.val:ℂ)*(g 1 1:ℂ)^(-(2:ℤ)))) := by
  have hdMatrix : 0<(g:Matrix (Fin 2) (Fin 2) ℝ).det := hd
  have he : (f ∣[(2:ℤ)] g) = (fun z : ℍ =>
      f (g • z)*(g.det.val:ℂ)*(g 1 1:ℂ)^(-(2:ℤ))) := by
    funext z
    simp [ModularForm.slash_apply,UpperHalfPlane.σ,hdMatrix,UpperHalfPlane.denom,hc,
      abs_of_pos hdMatrix]
  rw [he]
  exact ((hf.comp (UpperHalfPlane.tendsto_smul_atImInfty hc)).mul_const
    (g.det.val:ℂ)).mul_const ((g 1 1:ℂ)^(-(2:ℤ)))
end QEC.Coding.TannerLiftedProduct
