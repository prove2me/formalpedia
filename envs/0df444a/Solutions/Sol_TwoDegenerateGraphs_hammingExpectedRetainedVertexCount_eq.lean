-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedVertexCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/3570daa3-fe1a-4035-9709-55ad300f9110

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_vertex

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    hammingExpectedRetainedVertexCount dimension =
      2 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
  unfold hammingExpectedRetainedVertexCount
  simp_rw [hammingRetentionMeasure_real_contains_vertex]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring
end TwoDegenerateGraphs
