-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedVertexSquare_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/3b858038-02e3-43f3-b512-8f5c73330db1

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_vertexPair

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension =
      (((2 * 2 ^ dimension : ℕ) : ℝ) ^ 2) *
        hammingRetentionProbability dimension ^ 2 +
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        (hammingRetentionProbability dimension -
          hammingRetentionProbability dimension ^ 2) := by
  classical
  have hpoint
      (first second : Bool × HammingWord dimension) :
      (if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2) =
        hammingRetentionProbability dimension ^ 2 +
          (if first = second then
            hammingRetentionProbability dimension -
              hammingRetentionProbability dimension ^ 2
           else 0) := by
    by_cases hequal : first = second <;>
      simp [hequal]
  unfold hammingExpectedRetainedVertexSquare
  simp_rw [hammingRetentionMeasure_real_vertexPair,
    hpoint, Finset.sum_add_distrib]
  simp [HammingWord, nsmul_eq_mul]
  ring
end TwoDegenerateGraphs
