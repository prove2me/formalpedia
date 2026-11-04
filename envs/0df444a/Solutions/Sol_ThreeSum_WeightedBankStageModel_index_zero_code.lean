-- Prove2me | solution 1 for ThreeSum.WeightedBankStageModel.index_zero_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:08.51641+00:00
-- url     : https://prove2.me/submissions/658df7ec-e220-47a5-ad2a-ee729e023c1a

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_ThreeSum_WeightedBankStageModel_lowerWord_zero
import Theorems.Thm_ThreeSum_WeightedBankStageModel_index_spec
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_zeroCode_eq_update


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedBankStageModel
theorem _root_.solution {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (j : ℕ) (hj : j<n) :
    address (E.word (index E i 0 j))=
      LightTernaryCodes.zeroCode (2*N) (low i) (high i) (address (E.word j)) := by
  rw [(index_spec E i 0 j hj).2,lowerWord_zero,zeroCode_eq_update]
end ThreeSum.WeightedBankStageModel
