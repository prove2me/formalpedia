-- Prove2me | solution 1 for TwoDegenerateGraphs.eventually_manuscriptHammingRadius_binEntropy_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/70b90bb7-142a-4cbe-8bb3-bfd01443503e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_manuscriptHammingRadius_binEntropy_tendsto

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.binEntropy tau - loss ≤
        Real.binEntropy
          ((manuscriptHammingRadius dimension : ℝ) /
            (dimension : ℝ)) := by
  have hneighborhood :
      Set.Ioi (Real.binEntropy tau - loss) ∈
        𝓝 (Real.binEntropy tau) :=
    Ioi_mem_nhds (by linarith)
  filter_upwards
    [manuscriptHammingRadius_binEntropy_tendsto hneighborhood]
    with dimension hdimension
  exact (show Real.binEntropy tau - loss <
    Real.binEntropy
      ((manuscriptHammingRadius dimension : ℝ) /
        (dimension : ℝ)) from hdimension).le
end TwoDegenerateGraphs
