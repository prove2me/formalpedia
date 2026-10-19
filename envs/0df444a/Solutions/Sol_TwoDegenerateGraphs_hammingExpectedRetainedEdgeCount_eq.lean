-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedEdgeCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/7ab9a2ec-cb5d-4dc5-a710-7bc4f4dc1234

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_pair
import Theorems.Thm_TwoDegenerateGraphs_hammingWordEdge_sum_const

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeCount dimension radius =
      hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) := by
  classical
  have hpair (left right : HammingWord dimension) :
      (hammingRetentionMeasure dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained} =
        hammingRetentionProbability dimension ^ 2 :=
    hammingRetentionMeasure_real_contains_pair
      dimension (false, left) (true, right) (by simp)
  unfold hammingExpectedRetainedEdgeCount
  simp_rw [hpair]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    hammingWordEdge_sum_const dimension radius
      (hammingRetentionProbability dimension ^ 2)
end TwoDegenerateGraphs
