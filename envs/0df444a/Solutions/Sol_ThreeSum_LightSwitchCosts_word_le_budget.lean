-- Prove2me | solution 1 for ThreeSum.LightSwitchCosts.word_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:36:48.440883+00:00
-- url     : https://prove2.me/submissions/c755a85a-1b3f-45d3-9837-81abd1038bf8

import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Theorems.Thm_ThreeSum_LightSwitchCosts_residual_le_bits
import Theorems.Thm_ThreeSum_LightScales_blockCount_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchCosts
open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology
namespace ThreeSum.LightSwitchCosts
theorem _root_.solution (n j : ℕ) :
    LightSwitch.word (blockCount (inputBits n)) (Switch.residualSize n j) ≤ wordBudget n := by
  have hr := residual_le_bits n j
  have hJ := LightScales.blockCount_le (inputBits n)
  exact Nat.pow_le_pow_left (by omega) 64
end ThreeSum.LightSwitchCosts
