-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel.index_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:25.970444+00:00
-- url     : https://prove2.me/submissions/21bf3567-7860-4b2e-abf5-e236af68043b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStageModel
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_concrete_cost_mono
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_cost_mono


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel
theorem _root_.solution {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) :
    index E i e j<n ∧ E.word (index E i e j)=lowerWord (E.word j) i e := by
  unfold index
  rw [dif_pos hj]
  exact Classical.choose_spec (E.complete _ ((WeightedCache.cost_mono WeightedCache.concrete_cost_mono (lowerWord_below (E.word j) i e)).trans (E.mem j hj)))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel
