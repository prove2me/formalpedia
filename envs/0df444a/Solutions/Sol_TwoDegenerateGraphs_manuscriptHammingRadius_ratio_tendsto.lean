-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptHammingRadius_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/a643bddb-1d26-4b22-b906-42fcdaf9bdfb

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Tendsto
      (fun dimension : ℕ =>
        (manuscriptHammingRadius dimension : ℝ) / (dimension : ℝ))
      atTop (𝓝 tau) := by
  unfold manuscriptHammingRadius
  exact
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) tau_pos.le).comp
      tendsto_natCast_atTop_atTop
end TwoDegenerateGraphs
