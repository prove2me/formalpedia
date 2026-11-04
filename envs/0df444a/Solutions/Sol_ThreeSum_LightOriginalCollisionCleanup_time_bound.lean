-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionCleanup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:51:32.451399+00:00
-- url     : https://prove2.me/submissions/cfacbaaa-461d-4c32-9640-22dd9bfda0f7

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_bad_length_le_collisions

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalCollisionCleanup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightOriginalBucketFilter
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOriginalCollisionCleanup
theorem _root_.solution (keys : ℕ → ℕ) (n scanN L : ℕ) :
    time keys n scanN L≤200*n+400+
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card*
        (scanN*(120*L+330)+300) := by
  have hb := bad_length_le_collisions keys n
  have hm := Nat.mul_le_mul_right (scanN*(120*L+330)+300) hb
  unfold time LightOriginalBucketFilter.time LightDeletedTwoSum.time LightColoredTwoSum.time
    LightBandLookup.time LightBandLookup.searchTime
  nlinarith only [hm]
end ThreeSum.LightOriginalCollisionCleanup
