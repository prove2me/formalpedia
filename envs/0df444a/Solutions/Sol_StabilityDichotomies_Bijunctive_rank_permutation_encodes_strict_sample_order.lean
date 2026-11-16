-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.rank_permutation_encodes_strict_sample_order
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:20:09.975385+00:00
-- url     : https://prove2.me/submissions/af3266d9-e985-43d8-b0b0-d5e1e72ded4e

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem solution (n : ℕ) (x : Fin n → ℝ) (p : Equiv.Perm (Fin n))
    (h : ∀ i, (Finset.univ.filter (fun j : Fin n => x j < x i)).card = (p i).val) :
    ∀ i j, p i < p j ↔ x i < x j := by
  have key : ∀ i j, x i < x j →
      (Finset.univ.filter (fun k : Fin n => x k < x i)).card <
        (Finset.univ.filter (fun k : Fin n => x k < x j)).card := by
    intro i j hij
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [hij], by simp⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact lt_trans hk hij
  have key2 : ∀ i j, x j ≤ x i →
      (Finset.univ.filter (fun k : Fin n => x k < x j)).card ≤
        (Finset.univ.filter (fun k : Fin n => x k < x i)).card := by
    intro i j hij
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_of_lt_of_le hk hij
  intro i j
  rw [Fin.lt_def, ← h i, ← h j]
  constructor
  · intro hp
    by_contra hx
    push Not at hx
    exact absurd (key2 i j hx) (not_le.mpr hp)
  · exact key i j
