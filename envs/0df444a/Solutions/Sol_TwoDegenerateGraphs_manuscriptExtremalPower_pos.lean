-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptExtremalPower_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/3cfa1b75-8910-4713-b89e-27c8320e4ce7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_exponentGain_pos

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    0 < manuscriptExtremalPower := by
  unfold manuscriptExtremalPower
  linarith [exponentGain_pos]
end TwoDegenerateGraphs
