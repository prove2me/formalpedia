-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedEdgeVariance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/0b8b168a-da10-4cdd-bd26-ae5301fb4885

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeSquare_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  have hsecond := hammingExpectedRetainedEdgeSquare_le dimension radius
  linarith
end TwoDegenerateGraphs
