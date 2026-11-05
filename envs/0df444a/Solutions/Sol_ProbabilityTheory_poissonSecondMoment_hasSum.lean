-- Prove2me | solution 1 for ProbabilityTheory.poissonSecondMoment_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:19:50.14698+00:00
-- url     : https://prove2.me/submissions/8b70da61-ff3c-4fba-b947-52f62d55ea68

import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Definitions.Def_LeanLevy_Probability_Poisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Real Finset
open scoped NNReal ENNReal Nat
theorem solution (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ (↑n : ℝ) ^ 2 * (poissonMeasure r).real {n}) ((r : ℝ) ^ 2 + r) := by
  have h1 := poissonFactorialMoment2_hasSum r
  have h2 := poissonExpectation_hasSum r
  -- n² = n(n-1) + n, so E[X²] = E[X(X-1)] + E[X]
  convert h1.add h2 using 1
  ext n; ring
