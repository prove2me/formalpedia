-- Prove2me | solution 1 for ThreeSum.TernaryBankStageModel.min_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:57.708196+00:00
-- url     : https://prove2.me/submissions/cc5b585d-7433-42d6-adac-8fb097e1f0de

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryBankStageModel
theorem _root_.solution (q : Fin 3) : min (1 : Fin 3) q=clampOne q := by
  fin_cases q <;> decide
end ThreeSum.TernaryBankStageModel
