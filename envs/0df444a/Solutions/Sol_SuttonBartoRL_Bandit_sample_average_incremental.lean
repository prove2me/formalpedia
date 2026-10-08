-- Prove2me | solution 1 for SuttonBartoRL.Bandit.sample_average_incremental
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:41:25.50199+00:00
-- url     : https://prove2.me/submissions/42b30ceb-f657-442e-ace8-07b377c0dc9a

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_IncrementalEstimates

open SuttonBartoRL.Bandit in
theorem solution (R : ℕ → ℝ) (Q₁ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    sampleAverage R Q₁ (n + 1)
      = sampleAverage R Q₁ n + (1 / (n : ℝ)) * (R n - sampleAverage R Q₁ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp [sampleAverage]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hs : ∑ i ∈ Finset.Icc 1 (k + 1 + 1 + 1 - 1), R i
        = (∑ i ∈ Finset.Icc 1 (k + 1 + 1 - 1), R i) + R (k + 1 + 1) := by
      show ∑ i ∈ Finset.Icc 1 (k + 2), R i = (∑ i ∈ Finset.Icc 1 (k + 1), R i) + R (k + 2)
      rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [sampleAverage, show ¬ (k + 1 + 1 + 1 ≤ 1) by omega,
      show ¬ (k + 1 + 1 ≤ 1) by omega, if_false, hs]
    push_cast
    have h1 : ((k : ℝ) + 1 + 1 + 1 - 1) = k + 2 := by ring
    have h2 : ((k : ℝ) + 1 + 1 - 1) = k + 1 := by ring
    rw [h1, h2]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    have hk3 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring
