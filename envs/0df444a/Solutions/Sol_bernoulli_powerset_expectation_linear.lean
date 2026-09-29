-- Prove2me | solution 1 for bernoulli_powerset_expectation_linear
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T20:52:06.702242+00:00
-- url     : https://prove2.me/submissions/a1baf0a0-3ac7-432d-8f00-8c05788c60c7

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- `bernoulli_powerset_expectation_linear`.

**Linearity of expectation** over the coordinate sum: the expectation of a
statistic that is a sum of per-coordinate functions of the inclusion indicators
factorizes term-by-term, each term being the single-coordinate marginal
`p·g w 1 + (1-p)·g w 0`. Proved by distributing the weight into the inner sum,
swapping the order of summation (`Finset.sum_comm`), and applying the
single-coordinate marginal to each coordinate. -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ)
    (g : (Fin n₁ × Fin n₂) → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∑ w : Fin n₁ × Fin n₂, g w (if w ∈ Omega then 1 else 0)) =
      ∑ w : Fin n₁ × Fin n₂, (p * g w 1 + (1 - p) * g w 0) := by
  classical
  unfold bernoulliExpectation
  have hdist : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega *
        (∑ w : Fin n₁ × Fin n₂, g w (if w ∈ Omega then 1 else 0)) =
      ∑ w : Fin n₁ × Fin n₂,
        bernoulliObservationWeight p Omega * g w (if w ∈ Omega then 1 else 0) := by
    intro Omega; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun Omega _ => hdist Omega), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  have := bernoulli_powerset_expectation_single_coordinate (n₁ := n₁) (n₂ := n₂) p w (g w)
  unfold bernoulliExpectation at this
  exact this
