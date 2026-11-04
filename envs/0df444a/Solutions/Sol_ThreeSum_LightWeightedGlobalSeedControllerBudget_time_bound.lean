-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalSeedControllerBudget.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:34:55.854216+00:00
-- url     : https://prove2.me/submissions/141d6a65-c557-4b52-8c06-7851b48ebbaf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalSeedControllerBudget
namespace ThreeSum.LightWeightedGlobalSeedControllerBudget
theorem _root_.solution (n seedTime spanTime : ℕ) :
    LightWeightedGlobalSeedController.time n seedTime spanTime≤
      (n+1)*(seedTime+spanTime+2000) := by
  unfold LightWeightedGlobalSeedController.time LightTernaryRowSelector.time
  nlinarith
end ThreeSum.LightWeightedGlobalSeedControllerBudget
