-- Prove2me | solution 1 for bernoulli_event_prob_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T21:59:57.871471+00:00
-- url     : https://prove2.me/submissions/18d25c21-f0ce-475b-b270-7b802fc5e24c

import Definitions.Def_matrix_completion_bernoulli

open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ : ℕ} {p : ℝ}
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 → 0 ≤ bernoulliEventProb p Event := by
  intro hp0 hp1
  unfold bernoulliEventProb bernoulliObservationWeight
  refine Finset.sum_nonneg ?_
  intro Omega hOmega
  by_cases hEvent : Event Omega
  · simp [hEvent,
      mul_nonneg (pow_nonneg hp0 _)
        (pow_nonneg (sub_nonneg.mpr hp1) _)]
  · simp [hEvent]
