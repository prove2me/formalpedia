-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_slash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:02:00.006591+00:00
-- url     : https://prove2.me/submissions/38294fb8-a208-40d6-963d-fb5fa57062f0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
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
theorem _root_.solution (m : ℕ) (hm : 0<m) (r : ℝ) :
    (EisensteinSeries.E2 ∣[(2:ℤ)] lpsE2AffineMatrix m hm r)=
      (fun z : ℍ => (m:ℂ)*EisensteinSeries.E2 (lpsE2AffineMatrix m hm r • z)) := by
  funext z
  simp [ModularForm.slash_apply,UpperHalfPlane.σ,hm,UpperHalfPlane.denom,
    lpsE2AffineMatrix_coe,Matrix.of_apply,mul_comm]
end QEC.Coding.TannerLiftedProduct
