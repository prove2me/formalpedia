-- Prove2me | solution 1 for ThreeSum.TernaryBankStageModel.forwardStage_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:01:38.236629+00:00
-- url     : https://prove2.me/submissions/07e2f99e-d095-4fc0-95ba-18f0aec2a70a

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_succ


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryBankStageModel
theorem _root_.solution {N K : ℕ} (hK : K<N) (F : TritWord N→ℤ) :
    forwardStage (K+1) F=coordinateZeta ⟨K,hK⟩ (forwardStage K F) := by
  rw [forwardStage,coords_succ hK]
  rfl
end ThreeSum.TernaryBankStageModel
