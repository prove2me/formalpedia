-- Prove2me | solution 1 for ThreeSum.TernaryBankStageModel.lowerWord_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:56.561954+00:00
-- url     : https://prove2.me/submissions/e283b599-e96b-4df1-9e76-19bbdd6b7184

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
import Theorems.Thm_ThreeSum_TernaryBankStageModel_lowerWord_of_le
import Theorems.Thm_Light_LocalsBut_update


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryBankStageModel
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) :
    lowerWord R i 0=Function.update R i 0 := by
  apply lowerWord_of_le
  exact Fin.zero_le _
end ThreeSum.TernaryBankStageModel
