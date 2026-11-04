-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupedBanks.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:52.638671+00:00
-- url     : https://prove2.me/submissions/2368e36c-47c6-4af6-808d-b36f79f02406

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankStep
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedBanks

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
namespace ThreeSum.LightTernaryGroupedBanks
theorem _root_.solution : program.length=20 := rfl
end ThreeSum.LightTernaryGroupedBanks
