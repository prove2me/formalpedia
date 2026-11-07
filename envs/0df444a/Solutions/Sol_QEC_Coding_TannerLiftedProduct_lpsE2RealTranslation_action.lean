-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2RealTranslation_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:48:59.519145+00:00
-- url     : https://prove2.me/submissions/c955edc5-bb1a-47cd-90c4-d50d7d736c0d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (r : ℝ) (z : ℍ) :
    lpsE2RealTranslation r • z=r +ᵥ z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,UpperHalfPlane.coe_vadd]
  simp [lpsE2RealTranslation,Matrix.of_apply,add_comm]
end QEC.Coding.TannerLiftedProduct
