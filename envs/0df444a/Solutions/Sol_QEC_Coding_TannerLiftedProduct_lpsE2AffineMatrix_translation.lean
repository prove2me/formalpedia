-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_translation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:03:07.453648+00:00
-- url     : https://prove2.me/submissions/eed3e9ab-3db2-4275-b832-86f8a505ac10

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
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
theorem _root_.solution (m : ℕ) (hm : 0<m) (r : ℝ) (z : ℍ) :
    r +ᵥ (lpsE2AffineMatrix m hm 0 • z) = lpsE2AffineMatrix m hm r • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd,lpsE2AffineMatrix_action,lpsE2AffineMatrix_action]
  simp only [Complex.ofReal_zero,add_zero]
  ring
end QEC.Coding.TannerLiftedProduct
