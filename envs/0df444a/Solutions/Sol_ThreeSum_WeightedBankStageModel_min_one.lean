-- Prove2me | solution 1 for ThreeSum.WeightedBankStageModel.min_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:24:39.149212+00:00
-- url     : https://prove2.me/submissions/1354c742-50a9-4f91-b955-d97b1f7c57f3

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedBankStageModel
theorem _root_.solution (q : Fin 3) : min (1 : Fin 3) q=clampOne q := by
  fin_cases q <;> decide
end ThreeSum.WeightedBankStageModel
