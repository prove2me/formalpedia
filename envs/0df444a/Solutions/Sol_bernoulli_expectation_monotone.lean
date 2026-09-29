-- Prove2me | solution 1 for bernoulli_expectation_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T14:39:25.565801+00:00
-- url     : https://prove2.me/submissions/acc08853-8c13-4444-8b41-6b79f8eeac87

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Ring.Finset
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (F G : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ p → p ≤ 1 → (∀ Ω, F Ω ≤ G Ω) →
    bernoulliExpectation p F ≤ bernoulliExpectation p G := by
  intro hp0 hp1 hFG
  classical
  have hw : ∀ Ω : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Ω := by
    intro Ω
    unfold bernoulliObservationWeight
    have h1p : (0:ℝ) ≤ 1 - p := by linarith
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg h1p _)
  unfold bernoulliExpectation
  apply Finset.sum_le_sum
  intro Ω _
  exact mul_le_mul_of_nonneg_left (hFG Ω) (hw Ω)
