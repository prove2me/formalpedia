-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/13d34e41-ac09-4ab4-a297-d02cc48fa5da

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_manuscriptExpectedRetainedEdgeCount_tendsto_atTop

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    manuscriptExpectedRetainedEdgeCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]
end TwoDegenerateGraphs
