-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedVertexCount_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/f1ee3138-98a6-49a7-a1b3-ade91327812b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integrable
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_integral_event_indicator

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexCount dimension := by
  classical
  unfold hammingRetainedVertexCount hammingExpectedRetainedVertexCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun vertex _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if vertex ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro vertex _
  exact hammingRetentionMeasure_integral_event_indicator dimension
    {retained : Set (Bool × HammingWord dimension) | vertex ∈ retained}
end TwoDegenerateGraphs
