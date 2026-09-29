-- Prove2me | solution 1 for binomial_cardinality_probabilities_sum_to_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:08:33.057877+00:00
-- url     : https://prove2.me/submissions/dda091e0-d857-41ea-b864-256f8d56b9b2

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    (N : ℕ) (p : ℝ) :
    0 ≤ p → p ≤ 1 →
    (∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p) = 1 := by
  intro _ _
  have hpp : p + (1 - p) = 1 := by ring
  have h := add_pow p (1 - p) N
  rw [hpp, one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  unfold binomialCardinalityProb
  ring
