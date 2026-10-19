-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedVertexCount_inv_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/24ff933f-cf9f-4bb2-bcf6-613a4bbcf360

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexCount_tendsto_atTop

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedVertexCount dimension)
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingExpectedRetainedVertexCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]
end TwoDegenerateGraphs
