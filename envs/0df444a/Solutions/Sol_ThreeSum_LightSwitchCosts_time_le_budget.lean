-- Prove2me | solution 1 for ThreeSum.LightSwitchCosts.time_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:36:43.132414+00:00
-- url     : https://prove2.me/submissions/4f6f6d93-e554-4865-9314-b01eda5dc79b

import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Theorems.Thm_ThreeSum_LightSwitchCosts_residual_le_bits

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchCosts
open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology
namespace ThreeSum.LightSwitchCosts
theorem _root_.solution (n j : ℕ) :
    LightSwitch.time (Switch.residualSize n j) ≤ timeBudget n := by
  have hh := residual_le_bits n j
  unfold LightSwitch.time timeBudget
  omega
end ThreeSum.LightSwitchCosts
