-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionCleanup.surviving_keys_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:11.443208+00:00
-- url     : https://prove2.me/submissions/00545e0e-7fc5-49a1-ab97-7d4c645fc0ee

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_count_self_ne_one_iff

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
theorem _root_.solution {keys : ℕ → ℕ} {n i j : ℕ}
    (hi : i∈good keys (counts keys n) n) (hj : j∈good keys (counts keys n) n)
    (he : keys i=keys j) : i=j := by
  have hin := List.mem_range.mp (List.mem_filter.mp hi).1
  have hjn := List.mem_range.mp (List.mem_filter.mp hj).1
  have hc : counts keys n (keys i)=1 := of_decide_eq_true (List.mem_filter.mp hi).2
  by_contra hne
  exact ((count_self_ne_one_iff hin).mpr ⟨j,hjn,Ne.symm hne,he.symm⟩) hc
end ThreeSum.LightOriginalCollisionCleanup
