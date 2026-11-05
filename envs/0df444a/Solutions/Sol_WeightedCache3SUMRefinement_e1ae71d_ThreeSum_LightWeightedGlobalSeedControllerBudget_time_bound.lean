-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedControllerBudget.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:58:35.663219+00:00
-- url     : https://prove2.me/submissions/7a0edf06-0b90-4bc9-87e3-8be39c591af7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedControllerBudget

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedControllerBudget
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedControllerBudget
theorem _root_.solution (n seedTime spanTime : ℕ) :
    LightWeightedGlobalSeedController.time n seedTime spanTime≤
      (n+1)*(seedTime+spanTime+2000) := by
  unfold LightWeightedGlobalSeedController.time LightTernaryRowSelector.time
  nlinarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedControllerBudget
