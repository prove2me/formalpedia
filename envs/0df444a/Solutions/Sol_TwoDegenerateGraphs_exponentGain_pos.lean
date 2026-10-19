-- Prove2me | solution 1 for TwoDegenerateGraphs.exponentGain_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/3cb2af41-f7f3-4aa8-aa4d-f164b3c5d5e9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_midpointBeta_lt_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution : 0 < exponentGain := by
  unfold exponentGain
  exact div_pos certifiedWindowWidth_pos
    (mul_pos (by norm_num) (sub_pos.mpr midpointBeta_lt_one))
end TwoDegenerateGraphs
