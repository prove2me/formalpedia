-- Prove2me | solution 1 for TwoDegenerateGraphs.eventually_manuscriptVertexCount_power_le_extremalNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/b8266d18-f481-47d0-af43-05842a5d021e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_eventually_expectedRetainedEdge_le_extremalNumber
import Theorems.Thm_TwoDegenerateGraphs_eventually_manuscriptVertexCount_power_le_expectedRetainedEdge

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hextremal⟩ :=
    eventually_expectedRetainedEdge_le_extremalNumber
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards
    [eventually_manuscriptVertexCount_power_le_expectedRetainedEdge,
      hextremal] with dimension hpower hbound
  exact hpower.trans hbound
end TwoDegenerateGraphs
