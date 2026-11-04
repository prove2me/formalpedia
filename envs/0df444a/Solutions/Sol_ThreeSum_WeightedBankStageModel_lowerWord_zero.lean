-- Prove2me | solution 1 for ThreeSum.WeightedBankStageModel.lowerWord_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:24:38.022789+00:00
-- url     : https://prove2.me/submissions/9772cd8b-309a-46de-ac33-9880223d25c9

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_ThreeSum_WeightedBankStageModel_lowerWord_of_le
import Theorems.Thm_Light_LocalsBut_update


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedBankStageModel
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) :
    lowerWord R i 0=Function.update R i 0 := by
  apply lowerWord_of_le
  exact Fin.zero_le _
end ThreeSum.WeightedBankStageModel
