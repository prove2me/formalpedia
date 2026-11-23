-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.inner_gs_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:11.759806+00:00
-- url     : https://prove2.me/submissions/492f8d74-7800-4422-898d-ea635a037349

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (k : Fin d) {y : E} (hy : y ∈ span ℝ (b '' Set.Iio k)) :
    ⟪gs b k, y⟫_ℝ = 0 := by
  have hle : span ℝ (gramSchmidt ℝ b '' Set.Iio k) ≤ (ℝ ∙ gs b k)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact gramSchmidt_orthogonal ℝ b (ne_of_gt hi)
  rw [← span_gramSchmidt_Iio ℝ b k] at hy
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hy)
end ReciprocityTheory.ReducedBases.T2
