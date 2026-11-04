-- Prove2me | solution 1 for ThreeSum.TernaryOriginalCollisions.deleted_card_le_collisions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:34.602373+00:00
-- url     : https://prove2.me/submissions/7382ff50-3d59-4331-a397-e203837ddbc0

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalCollisions
open Finset TernaryOriginalRowMenu
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E B W : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Algebra K E] [Fintype E] [DecidableEq E]
  [Fintype B] [DecidableEq B] [DecidableEq W]
namespace ThreeSum.TernaryOriginalCollisions
theorem _root_.solution (hash : B → W) :
    (deleted hash).card ≤ (collisionPairs hash).card := by
  let partner : (deleted hash) → B := fun a => Classical.choose (mem_filter.mp a.property).2
  let f : (deleted hash) → (collisionPairs hash) := fun a =>
    ⟨(a.val,partner a),mem_filter.mpr ⟨mem_univ _,Classical.choose_spec (mem_filter.mp a.property).2⟩⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun c : collisionPairs hash => c.val.1) h
  simpa using Fintype.card_le_of_injective f hf
end ThreeSum.TernaryOriginalCollisions
