-- Prove2me | solution 1 for ThreeSum.LightTernaryWantedRows.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:05:09.037301+00:00
-- url     : https://prove2.me/submissions/71e69f59-909f-4df0-8966-2e2d6b5c2a90

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRowDispatch
import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedState
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRows

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedRows
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryWantedRowDispatch ThreeSum.LightTernaryPreparedState
set_option maxHeartbeats 7000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryWantedRows
theorem _root_.solution : program.length=30 := rfl
end ThreeSum.LightTernaryWantedRows
