-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptHammingRadius_binEntropy_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/0005d6af-b8d2-4983-933b-9bcd8ce112ad

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_manuscriptHammingRadius_ratio_tendsto

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Tendsto
      (fun dimension : ℕ =>
        Real.binEntropy
          ((manuscriptHammingRadius dimension : ℝ) / (dimension : ℝ)))
      atTop (𝓝 (Real.binEntropy tau)) := by
  exact Real.binEntropy_continuous.continuousAt.tendsto.comp
    manuscriptHammingRadius_ratio_tendsto
end TwoDegenerateGraphs
