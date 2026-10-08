-- Prove2me | solution 1 for SuttonBartoRL.Bandit.constant_step_weighted_average
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:07:38.396052+00:00
-- url     : https://prove2.me/submissions/59cb23e2-65fb-4824-bb0a-51c7ef6eb3ce

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_IncrementalEstimates

open SuttonBartoRL.Bandit in
theorem solution (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (Q R : ℕ → ℝ)
    (hQ : ∀ n : ℕ, 1 ≤ n → Q (n + 1) = Q n + α * (R n - Q n)) (n : ℕ) :
    Q (n + 1) = (1 - α) ^ n * Q 1 + ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) * R i ∧
      (1 - α) ^ n + ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : ∑ i ∈ Finset.Icc 1 (k + 1), α * (1 - α) ^ (k + 1 - i) * R i
        = (1 - α) * ∑ i ∈ Finset.Icc 1 k, α * (1 - α) ^ (k - i) * R i + α * R (k + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Icc] at hi
        rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
        ring
      · simp
    have e2 : ∑ i ∈ Finset.Icc 1 (k + 1), α * (1 - α) ^ (k + 1 - i)
        = (1 - α) * ∑ i ∈ Finset.Icc 1 k, α * (1 - α) ^ (k - i) + α := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Icc] at hi
        rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
        ring
      · simp
    constructor
    · rw [hQ (k + 1) (by omega), e1]
      linear_combination (1 - α) * h1
    · rw [e2]
      linear_combination (1 - α) * h2
