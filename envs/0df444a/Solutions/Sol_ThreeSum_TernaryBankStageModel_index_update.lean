-- Prove2me | solution 1 for ThreeSum.TernaryBankStageModel.index_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:06:26.020978+00:00
-- url     : https://prove2.me/submissions/54b942b3-38aa-419f-bfce-37387f94469e

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
import Theorems.Thm_ThreeSum_TernaryBankStageModel_lowerWord_of_le
import Theorems.Thm_ThreeSum_TernaryBankStageModel_index_spec
import Theorems.Thm_Light_LocalsBut_update


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryBankStageModel
theorem _root_.solution {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) (he : e≤E.word j i) :
    E.word (index E i e j)=Function.update (E.word j) i e :=
  (index_spec E i e j hj).2.trans (lowerWord_of_le _ _ _ he)
end ThreeSum.TernaryBankStageModel
