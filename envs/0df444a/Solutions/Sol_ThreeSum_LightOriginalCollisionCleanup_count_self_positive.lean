-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionCleanup.count_self_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:41.178143+00:00
-- url     : https://prove2.me/submissions/b483fd38-8dae-4a6e-ad33-3d7e660d3996

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalCollisionCleanup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightOriginalBucketFilter
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
namespace ThreeSum.LightOriginalCollisionCleanup
theorem _root_.solution {keys : ℕ → ℕ} {n i : ℕ} (hi : i<n) : 0<counts keys n (keys i) := by
  change 0<((Finset.range n).filter (fun j => keys j=keys i)).card
  apply Finset.card_pos.mpr
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,rfl⟩⟩
end ThreeSum.LightOriginalCollisionCleanup
