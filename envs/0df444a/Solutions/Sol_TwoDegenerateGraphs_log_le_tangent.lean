-- Prove2me | solution 1 for TwoDegenerateGraphs.log_le_tangent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/4905ec53-70b4-43b2-a051-dbc067856636

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hc)
  rw [Real.log_div hx.ne' hc.ne'] at hlog
  linarith
end TwoDegenerateGraphs
