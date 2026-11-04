-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivorPair.solution_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:58.200588+00:00
-- url     : https://prove2.me/submissions/76a6d25f-d8ff-498c-baed-c5ac2ef0e171

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_cleanupFlag_eq_one_iff
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_colored_decomposition
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_colored_decomposition


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits}
namespace ThreeSum.LightOriginalSurvivorPair
theorem _root_.solution (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i < nA, ∃ j < nB, ∃ k < nC, C k = A i+B j) ↔
      cleanupFlag A B C keysB keysC nA nB nC = 1 ∨
      ∃ i < nA, ∃ j < (indices keysB nB).length, ∃ k < (indices keysC nC).length,
        C (index keysC nC k) = A i+B (index keysB nB j) := by
  rw [cleanupFlag_eq_one_iff,or_assoc]
  exact LightOriginalSurvivors.colored_decomposition _ _ _ _ _ _ _ _
end ThreeSum.LightOriginalSurvivorPair
