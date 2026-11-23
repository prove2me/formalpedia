-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.gs_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:18.472797+00:00
-- url     : https://prove2.me/submissions/1079ff01-7ad5-4849-a9c1-87ed267273d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_sub_gs_mem
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_span

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
theorem _root_.solution (b : Fin d → E) (k : Fin d) (v : E) (h1 : b k - v ∈ span ℝ (b '' Set.Iio k))
    (h2 : ∀ j < k, ⟪v, b j⟫_ℝ = 0) : gs b k = v := by
  have hle : span ℝ (b '' Set.Iio k) ≤ (ℝ ∙ v)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact h2 j hj
  have hmem : gs b k - v ∈ span ℝ (b '' Set.Iio k) := by
    have h3 := Submodule.sub_mem _ h1 (b_sub_gs_mem b k)
    have h4 : b k - v - (b k - gs b k) = gs b k - v := by abel
    rwa [h4] at h3
  have h0 : ⟪gs b k - v, gs b k - v⟫_ℝ = 0 := by
    rw [inner_sub_left, inner_gs_span b k hmem,
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hmem), sub_zero]
  rw [← sub_eq_zero]
  exact inner_self_eq_zero.1 h0
end ReciprocityTheory.ReducedBases.T2
