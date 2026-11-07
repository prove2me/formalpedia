-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2_real_shift_mdifferentiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:30.665588+00:00
-- url     : https://prove2.me/submissions/6bac69c3-fc47-4d39-a5d9-82cf0048a730

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2RealTranslation_action
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
theorem _root_.solution (r : ℝ) :
    MDiff (fun z : ℍ => EisensteinSeries.E2 (r +ᵥ z)) := by
  have hpos : 0<(Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r)).det.val := by
    simp
  have h := E2_mdifferentiable.comp (UpperHalfPlane.mdifferentiable_smul hpos)
  have he : (fun z : ℍ => EisensteinSeries.E2
      (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z)) =
      (fun z : ℍ => EisensteinSeries.E2 (r +ᵥ z)) := by
    funext z
    apply congrArg EisensteinSeries.E2
    change lpsE2RealTranslation r • z=r +ᵥ z
    exact lpsE2RealTranslation_action r z
  change MDiff (fun z : ℍ => EisensteinSeries.E2
    (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z)) at h
  rw [he] at h
  exact h
end QEC.Coding.TannerLiftedProduct
