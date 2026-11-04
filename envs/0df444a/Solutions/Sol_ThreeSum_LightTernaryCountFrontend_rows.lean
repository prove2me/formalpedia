-- Prove2me | solution 1 for ThreeSum.LightTernaryCountFrontend.rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:11:44.964243+00:00
-- url     : https://prove2.me/submissions/04d5f1f9-32d7-4489-9301-8bbb26b05f4c

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
theorem _root_.solution : program[49]?=some (LightTernaryWantedRows.body 48) := rfl
end ThreeSum.LightTernaryCountFrontend
