-- Prove2me | solution 1 for ThreeSum.LightTernaryFinalPreparation.time_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:09.200682+00:00
-- url     : https://prove2.me/submissions/11a6290f-41dd-4c3b-9932-755311530432

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Theorems.Thm_ThreeSum_LightOriginalCollisionScore_time_eq


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryFinalPreparation
open Light LightSubsetAddress
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000
variable {lim : Limits}
namespace ThreeSum.LightTernaryFinalPreparation
theorem _root_.solution (nB nC q W : ℕ) : time nB nC q W = 74*(nB+nC)+26*q+17*W+659 := by
  unfold time
  rw [LightOriginalCollisionScore.time_eq,LightOriginalCollisionScore.time_eq]
  unfold powTableTime
  ring
end ThreeSum.LightTernaryFinalPreparation
