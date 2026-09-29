-- Prove2me | solution 1 for bernoulli_event_failure_decomposition_from_success_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:10:17.023251+00:00
-- url     : https://prove2.me/submissions/0131b519-8bc7-4c23-aff2-f5d99208d855

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p Event =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          fixedCardinalityEventProb k Event →
    (∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p) = 1 →
    1 - bernoulliEventProb p Event =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          (1 - fixedCardinalityEventProb k Event) := by
  intro _ _ hdec hsum
  rw [hdec]
  rw [show (∑ k ∈ Finset.range (n₁ * n₂ + 1),
            binomialCardinalityProb (n₁ * n₂) k p *
              (1 - fixedCardinalityEventProb k Event))
        = (∑ k ∈ Finset.range (n₁ * n₂ + 1), binomialCardinalityProb (n₁ * n₂) k p)
          - ∑ k ∈ Finset.range (n₁ * n₂ + 1),
              binomialCardinalityProb (n₁ * n₂) k p * fixedCardinalityEventProb k Event
        from by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring]
  rw [hsum]
