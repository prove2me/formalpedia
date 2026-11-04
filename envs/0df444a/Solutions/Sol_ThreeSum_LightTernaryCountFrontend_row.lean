-- Prove2me | solution 1 for ThreeSum.LightTernaryCountFrontend.row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:11:43.373448+00:00
-- url     : https://prove2.me/submissions/098c3311-9dfc-4bb1-bba0-9c349a5a5869

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankResources
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRows
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryWantedRowDispatch ThreeSum.LightTernaryPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000
namespace ThreeSum.LightTernaryCountFrontend
theorem _root_.solution : program[48]?=some (LightTernaryWantedRowDispatch.body 47) := rfl
end ThreeSum.LightTernaryCountFrontend
