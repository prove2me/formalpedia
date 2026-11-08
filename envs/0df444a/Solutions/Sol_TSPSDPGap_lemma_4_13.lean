-- Prove2me | solution 1 for TSPSDPGap.lemma_4_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:25:09.167634+00:00
-- url     : https://prove2.me/submissions/92f5bde2-7b31-4b21-991b-e2a8f7afe752

import Mathlib

theorem solution (θ : ℝ) (g : ℕ) :
    (2 * Real.cos θ - 2) * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ) =
      Real.cos (g * θ) - g * Real.cos θ + ((g : ℝ) - 1) := by
  have hC : ∀ g : ℕ, (2 * Real.cos θ - 2) * ∑ j ∈ Finset.Ico 1 (g + 1), Real.cos (j * θ) =
      Real.cos (((g : ℝ) + 1) * θ) - Real.cos ((g : ℝ) * θ) - Real.cos θ + 1 := by
    intro g
    induction g with
    | zero => simp
    | succ g ih =>
      rw [Finset.sum_Ico_succ_top (by omega), mul_add, ih]
      push_cast
      have h1 : Real.cos (((g : ℝ) + 1 + 1) * θ) =
          Real.cos (((g : ℝ) + 1) * θ) * Real.cos θ - Real.sin (((g : ℝ) + 1) * θ) * Real.sin θ := by
        rw [show ((g : ℝ) + 1 + 1) * θ = ((g : ℝ) + 1) * θ + θ by ring, Real.cos_add]
      have h2 : Real.cos ((g : ℝ) * θ) =
          Real.cos (((g : ℝ) + 1) * θ) * Real.cos θ + Real.sin (((g : ℝ) + 1) * θ) * Real.sin θ := by
        rw [show (g : ℝ) * θ = ((g : ℝ) + 1) * θ - θ by ring, Real.cos_sub]
      linear_combination (-1 : ℝ) * h1 - h2
  induction g with
  | zero => simp
  | succ g ih =>
    have hsplit : ∑ j ∈ Finset.Ico 1 (g + 1), (((g + 1 : ℕ) : ℝ) - j) * Real.cos (j * θ) =
        ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ) +
          ∑ j ∈ Finset.Ico 1 (g + 1), Real.cos (j * θ) := by
      rw [show ∑ j ∈ Finset.Ico 1 (g + 1), (((g + 1 : ℕ) : ℝ) - j) * Real.cos (j * θ) =
          ∑ j ∈ Finset.Ico 1 (g + 1), (((g : ℝ) - j) * Real.cos (j * θ) + Real.cos (j * θ)) from
          Finset.sum_congr rfl (fun j _ => by push_cast; ring), Finset.sum_add_distrib]
      congr 1
      rcases Nat.eq_zero_or_pos g with h | h
      · subst h
        simp
      · rw [Finset.sum_Ico_succ_top (by omega)]
        simp
    rw [hsplit, mul_add, ih, hC g]
    push_cast
    ring
