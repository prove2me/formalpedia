-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:51:58.656275+00:00
-- url     : https://prove2.me/submissions/8321d1a8-a0b8-48ff-b93f-073d587f1865

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_add_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (z : ℍ) :
    lpsQuadraticE2Twist q ((1:ℝ) +ᵥ z)=lpsQuadraticE2Twist q z := by
  unfold lpsQuadraticE2Twist
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [show ((a.val:ℝ)/(q:ℝ)) +ᵥ ((1:ℝ) +ᵥ z) =
    (1:ℝ) +ᵥ (((a.val:ℝ)/(q:ℝ)) +ᵥ z) by
      rw [← add_vadd,← add_vadd,add_comm],lpsE2_add_one]
end QEC.Coding.TannerLiftedProduct
