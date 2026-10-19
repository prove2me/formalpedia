-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptExpectedRetainedEdgeCount_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/5fb91e1b-5fb4-49ca-9654-4d901c4da8ac

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_exp_mul_div_nat_succ_tendsto_atTop
import Theorems.Thm_TwoDegenerateGraphs_sampledHammingEdgeEntropyRate_pos
import Theorems.Thm_TwoDegenerateGraphs_eventually_manuscriptExpectedRetainedEdge_entropy_lower

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Tendsto
      (fun dimension : ℕ =>
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension))
      atTop atTop := by
  have hrate := sampledHammingEdgeEntropyRate_pos
  have hloss : 0 < sampledHammingEdgeEntropyRate / 2 := by
    positivity
  have hlower := eventually_manuscriptExpectedRetainedEdge_entropy_lower
    (sampledHammingEdgeEntropyRate / 2) hloss
  have hgrowth := exp_mul_div_nat_succ_tendsto_atTop
    (sampledHammingEdgeEntropyRate / 2) hloss
  have hhalf :
      sampledHammingEdgeEntropyRate -
          sampledHammingEdgeEntropyRate / 2 =
        sampledHammingEdgeEntropyRate / 2 := by
    ring
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hlower] with dimension hdimension
  simpa only [hhalf, mul_comm] using hdimension
end TwoDegenerateGraphs
