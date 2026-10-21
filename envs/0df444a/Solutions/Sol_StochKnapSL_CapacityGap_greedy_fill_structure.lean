-- Prove2me | solution 1 for StochKnapSL.CapacityGap.greedy_fill_structure
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:38:56.544916+00:00
-- url     : https://prove2.me/submissions/34830a58-35d6-4232-a6f7-35a36897dc17

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory
open StochKnapSL.CapacityGap

theorem solution {N : ℕ} (σ : Equiv.Perm (Fin N)) (Q : ℝ) (x : Fin N → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hQ : 0 ≤ Q) :
    {i : Fin N | fill σ Q x i ≠ 0 ∧ fill σ Q x i ≠ x i}.Subsingleton ∧
      ∀ i, 0 < x i → (0 < fill σ Q x i ↔ ∑ j ∈ ahead σ i, x j < Q) := by
  -- key: a fractional customer has `0 < Q - S_i < x_i`
  have frac : ∀ i, fill σ Q x i ≠ 0 → fill σ Q x i ≠ x i →
      0 < Q - ∑ j ∈ ahead σ i, x j ∧ Q - ∑ j ∈ ahead σ i, x j < x i := by
    intro i h1 h2
    unfold fill at h1 h2
    set S := ∑ j ∈ ahead σ i, x j
    have hlt : max 0 (Q - S) < x i := by
      by_contra h; push_neg at h; exact h2 (min_eq_left h)
    have hm : min (x i) (max 0 (Q - S)) = max 0 (Q - S) := min_eq_right hlt.le
    rw [hm] at h1
    refine ⟨?_, lt_of_le_of_lt (le_max_right _ _) hlt⟩
    by_contra h; push_neg at h; exact h1 (max_eq_left h)
  -- if `i` is ahead of `j` then `S_j ≥ S_i + x_i`
  have mono : ∀ i j, σ.symm i < σ.symm j →
      ∑ k ∈ ahead σ i, x k + x i ≤ ∑ k ∈ ahead σ j, x k := by
    intro i j hij
    have hni : i ∉ ahead σ i := by simp [ahead]
    have hsub : insert i (ahead σ i) ⊆ ahead σ j := by
      intro k hk
      rw [Finset.mem_insert] at hk
      simp only [ahead, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rcases hk with rfl | hk
      · exact hij
      · exact lt_trans hk hij
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hx k)
    rw [Finset.sum_insert hni] at this
    linarith
  refine ⟨?_, ?_⟩
  · intro i hi j hj
    obtain ⟨ai, bi⟩ := frac i hi.1 hi.2
    obtain ⟨aj, bj⟩ := frac j hj.1 hj.2
    by_contra hne
    have hne' : σ.symm i ≠ σ.symm j := fun h => hne (σ.symm.injective h)
    rcases lt_or_gt_of_ne hne' with h | h
    · have := mono i j h; linarith
    · have := mono j i h; linarith
  · intro i hxi
    unfold fill
    constructor
    · intro h
      have := lt_of_lt_of_le h (min_le_right _ _)
      by_contra h'; push_neg at h'
      rw [max_eq_left (by linarith)] at this; exact lt_irrefl _ this
    · intro h
      apply lt_min hxi
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
