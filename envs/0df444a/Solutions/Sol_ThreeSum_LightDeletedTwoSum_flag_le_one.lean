-- Prove2me | solution 1 for ThreeSum.LightDeletedTwoSum.flag_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:49.567726+00:00
-- url     : https://prove2.me/submissions/5a5dcb8a-b724-441d-99ef-c0588fecbff3

import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightDeletedTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
namespace ThreeSum.LightDeletedTwoSum
theorem _root_.solution (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) :
    flag ids values scan target targetN scanN j sign≤1 := by unfold flag; split <;> omega
end ThreeSum.LightDeletedTwoSum
