-- Prove2me | solution 1 for ThreeSum.WeightedBankStageModel.index_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:46:16.291579+00:00
-- url     : https://prove2.me/submissions/41b3b296-c05f-467f-82b2-488d963d9959

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_WeightedCache_concrete_cost_mono
import Theorems.Thm_WeightedCache_cost_mono


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedBankStageModel
theorem _root_.solution {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) :
    index E i e j<n ∧ E.word (index E i e j)=lowerWord (E.word j) i e := by
  unfold index
  rw [dif_pos hj]
  exact Classical.choose_spec (E.complete _ ((WeightedCache.cost_mono WeightedCache.concrete_cost_mono (lowerWord_below (E.word j) i e)).trans (E.mem j hj)))
end ThreeSum.WeightedBankStageModel
