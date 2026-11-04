-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryStages.stageValue_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:11.658544+00:00
-- url     : https://prove2.me/submissions/77dc7237-87c1-4713-8b26-43bac8ef61bc

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_succ
import Theorems.Thm_Light_LocalsBut_update


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryFrozenQueryStages
theorem _root_.solution {N K : ℕ} (hK : K<N) (H : TritWord N→ℤ) (R : TritWord N) :
    stageValue (K+1) H R =
      inverseDigit (fun d => stageValue K H (Function.update R ⟨K,hK⟩ d)) (R ⟨K,hK⟩) := by
  rw [stageValue,coords_succ hK]
  rfl
end ThreeSum.TernaryFrozenQueryStages
