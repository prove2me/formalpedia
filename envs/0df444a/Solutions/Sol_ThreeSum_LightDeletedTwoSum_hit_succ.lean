-- Prove2me | solution 1 for ThreeSum.LightDeletedTwoSum.hit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:29.222192+00:00
-- url     : https://prove2.me/submissions/0a37daf3-2133-459b-baad-256e08a02ee2

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
    Hit ids values scan target targetN scanN (j+1) sign ↔
      Hit ids values scan target targetN scanN j sign ∨
        LightColoredTwoSum.Hit scan target targetN scanN (values (ids j)) sign := by
  unfold Hit
  constructor
  · rintro ⟨i,hi,hh⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inl ⟨i,hi,hh⟩
    · exact Or.inr hh
  · rintro (⟨i,hi,hh⟩ | hh)
    · exact ⟨i,by omega,hh⟩
    · exact ⟨j,by omega,hh⟩
end ThreeSum.LightDeletedTwoSum
