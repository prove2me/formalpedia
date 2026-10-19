-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_variance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/3624f6c4-516b-4158-b440-22b488f97624

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeVariance_le
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_variance_eq

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  rw [hammingRetainedEdgeCount_variance_eq]
  exact hammingExpectedRetainedEdgeVariance_le dimension radius
end TwoDegenerateGraphs
