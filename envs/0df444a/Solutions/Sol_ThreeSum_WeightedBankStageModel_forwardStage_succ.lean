-- Prove2me | solution 1 for ThreeSum.WeightedBankStageModel.forwardStage_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:59:13.926667+00:00
-- url     : https://prove2.me/submissions/b3534785-e466-4247-8c69-c40c49721848

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_succ


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedBankStageModel
theorem _root_.solution {N K : ℕ} (hK : K<N) (F : TritWord N→ℤ) :
    forwardStage (K+1) F=coordinateZeta ⟨K,hK⟩ (forwardStage K F) := by
  rw [forwardStage,coords_succ hK]
  rfl
end ThreeSum.WeightedBankStageModel
