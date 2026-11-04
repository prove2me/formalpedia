-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixFinish.step_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:00:37.47226+00:00
-- url     : https://prove2.me/submissions/e3867366-a8e5-499e-bab8-6d7903f49f75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFullController
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixProgramLibrary
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Theorems.Thm_Light_Ends_call


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixFinish
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalPrefixFinish
theorem _root_.solution : stepBody = (
    .call 196 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16] 19 ;; body) :=rfl
end ThreeSum.LightWeightedGlobalPrefixFinish
