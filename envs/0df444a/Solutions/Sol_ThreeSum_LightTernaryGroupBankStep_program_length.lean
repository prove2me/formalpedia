-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupBankStep.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:10.439958+00:00
-- url     : https://prove2.me/submissions/b0bf3e5d-09e3-4687-a351-b0e5f2cd3080

import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankStep

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}
namespace ThreeSum.LightTernaryGroupBankStep
theorem _root_.solution : program.length=19 := by rfl
end ThreeSum.LightTernaryGroupBankStep
