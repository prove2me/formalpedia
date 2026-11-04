-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalArenaTemplate.seedFields_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:50:39.983791+00:00
-- url     : https://prove2.me/submissions/d2d2a22e-2108-4c85-a7ed-18dd3543e150

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.LightWeightedGlobalArenaTemplate
theorem _root_.solution : seedFields.length=48 := rfl
end ThreeSum.LightWeightedGlobalArenaTemplate
