-- Prove2me | solution 1 for ThreeSum.WeightedBankStageModel.index_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:42.101437+00:00
-- url     : https://prove2.me/submissions/8c543fea-4ea7-4f78-babe-15853eb00e5f

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_ThreeSum_WeightedBankStageModel_lowerWord_of_le
import Theorems.Thm_ThreeSum_WeightedBankStageModel_index_spec
import Theorems.Thm_Light_LocalsBut_update


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedBankStageModel
theorem _root_.solution {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) (he : e≤E.word j i) :
    E.word (index E i e j)=Function.update (E.word j) i e :=
  (index_spec E i e j hj).2.trans (lowerWord_of_le _ _ _ he)
end ThreeSum.WeightedBankStageModel
