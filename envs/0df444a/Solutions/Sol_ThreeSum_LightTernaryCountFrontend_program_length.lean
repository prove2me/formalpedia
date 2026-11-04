-- Prove2me | solution 1 for ThreeSum.LightTernaryCountFrontend.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:19:44.671395+00:00
-- url     : https://prove2.me/submissions/6162e537-55a2-429d-82b6-f04ece49b33e

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
theorem _root_.solution : program.length=52 := rfl
end ThreeSum.LightTernaryCountFrontend
