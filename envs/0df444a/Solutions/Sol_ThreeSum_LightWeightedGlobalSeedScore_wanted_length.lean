-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalSeedScore.wanted_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:23:54.978544+00:00
-- url     : https://prove2.me/submissions/12792d23-19c8-4181-8c34-d104f4563d81

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScore
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.LightWeightedGlobalSeedScore
theorem _root_.solution (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (LightTernaryWantedBatch.program p R S raws words maps).length=5 := rfl
end ThreeSum.LightWeightedGlobalSeedScore
