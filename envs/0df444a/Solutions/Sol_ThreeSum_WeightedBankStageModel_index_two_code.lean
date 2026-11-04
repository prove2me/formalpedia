-- Prove2me | solution 1 for ThreeSum.WeightedBankStageModel.index_two_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:54.826235+00:00
-- url     : https://prove2.me/submissions/a1fb7192-e1d1-4ead-9fc3-785ed8520680

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_ThreeSum_WeightedBankStageModel_lowerWord_two
import Theorems.Thm_ThreeSum_WeightedBankStageModel_index_spec

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedBankStageModel
theorem _root_.solution {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (j : ℕ) (hj : j<n) : address (E.word (index E i 2 j))=address (E.word j) := by
  rw [(index_spec E i 2 j hj).2,lowerWord_two]
end ThreeSum.WeightedBankStageModel
