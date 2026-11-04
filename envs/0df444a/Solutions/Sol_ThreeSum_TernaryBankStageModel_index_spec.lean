-- Prove2me | solution 1 for ThreeSum.TernaryBankStageModel.index_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:55:30.031907+00:00
-- url     : https://prove2.me/submissions/64978257-754f-4aa1-8925-89cb4714a657

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
import Theorems.Thm_ThreeSum_TernaryBank_rank_mono


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryBankStageModel
theorem _root_.solution {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) :
    index E i e j<n ∧ E.word (index E i e j)=lowerWord (E.word j) i e := by
  unfold index
  rw [dif_pos hj]
  exact Classical.choose_spec (E.complete _ ((rank_mono (lowerWord_below (E.word j) i e)).trans (E.mem j hj)))
end ThreeSum.TernaryBankStageModel
