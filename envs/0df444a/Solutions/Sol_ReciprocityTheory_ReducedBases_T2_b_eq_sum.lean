-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.b_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:03.324926+00:00
-- url     : https://prove2.me/submissions/7e581032-6c0a-4037-b4bd-c39b072da66e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_orth
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
private lemma inner_gs_sum_smul_gs (b : Fin d → E) (x : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ k, x k • gs b k⟫_ℝ = x j * ‖gs b j‖ ^ 2 := by
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  · intro k _ hk
    rw [real_inner_smul_right, gs_orth b (Ne.symm hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h
private lemma eq_zero_of_mem_span_gs_of_inner_eq_zero (b : Fin d → E) {y : E} (hy : y ∈ span ℝ (Set.range (gs b)))
    (h : ∀ j, ⟪gs b j, y⟫_ℝ = 0) : y = 0 := by
  have hle : span ℝ (Set.range (gs b)) ≤ (ℝ ∙ y)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact h j
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hy))
private lemma mu_mul_norm_gs_sq (b : Fin d → E) (hb : LinearIndependent ℝ b) (i j : Fin d) :
    mu b i j * ‖gs b j‖ ^ 2 = ⟪gs b j, b i⟫_ℝ := by
  have hne : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  unfold mu
  first
    | exact div_mul_cancel₀ _ hne
    | field_simp
end ReciprocityTheory.ReducedBases.T2
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (i : Fin d) :
    b i = ∑ j, mu b i j • gs b j := by
  rw [← sub_eq_zero]
  apply eq_zero_of_mem_span_gs_of_inner_eq_zero b
  · refine Submodule.sub_mem _ ?_ ?_
    · exact span_mono (Set.image_subset_range _ _) (mem_span_gramSchmidt ℝ b le_rfl)
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)
  · intro j
    rw [inner_sub_right, inner_gs_sum_smul_gs, mu_mul_norm_gs_sq b hb, sub_self]
end ReciprocityTheory.ReducedBases.T2
