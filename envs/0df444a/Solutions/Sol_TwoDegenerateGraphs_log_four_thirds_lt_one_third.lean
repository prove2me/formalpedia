-- Prove2me | solution 1 for TwoDegenerateGraphs.log_four_thirds_lt_one_third
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/94c1c955-9c2d-4a83-8009-1b205f02232d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Real.log ((4 : ℝ) / 3) < (1 : ℝ) / 3 := by
  have hlog := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
    (show (4 : ℝ) / 3 ≠ 1 by norm_num)
  norm_num at hlog ⊢
  linarith
end TwoDegenerateGraphs
