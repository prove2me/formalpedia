-- Prove2me | solution 1 for bernoulli_event_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:09:11.064467+00:00
-- url     : https://prove2.me/submissions/d7bd8a03-9be5-4835-9a0e-ee16b9b6bce4

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (EventA EventB : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ Omega, EventA Omega → EventB Omega) →
    bernoulliEventProb p EventA ≤ bernoulliEventProb p EventB := by
  intro hp0 hp1 hAB
  have hw : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  unfold bernoulliEventProb
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hA : EventA Omega
  · rw [if_pos hA, if_pos (hAB Omega hA)]
  · rw [if_neg hA]
    by_cases hB : EventB Omega
    · rw [if_pos hB]; exact hw Omega
    · rw [if_neg hB]
