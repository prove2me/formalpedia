-- Prove2me | solution 1 for ThreeSum.LightColoredTwoSum.hit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:54:58.2978+00:00
-- url     : https://prove2.me/submissions/ea73389b-281a-4e6f-b0f2-293bd1b6e871

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
namespace ThreeSum.LightColoredTwoSum
theorem _root_.solution (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) :
    Hit scan target m (j+1) bad sign ↔ Hit scan target m j bad sign ∨ ∃ k<m, target k=sign*scan j+bad := by
  unfold Hit
  constructor
  · rintro ⟨i,hi,k,hk,he⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inl ⟨i,hi,k,hk,he⟩
    · exact Or.inr ⟨k,hk,he⟩
  · rintro (⟨i,hi,k,hk,he⟩ | ⟨k,hk,he⟩)
    · exact ⟨i,by omega,k,hk,he⟩
    · exact ⟨j,by omega,k,hk,he⟩
end ThreeSum.LightColoredTwoSum
