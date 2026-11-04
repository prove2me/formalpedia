-- Prove2me | solution 1 for ThreeSum.TernaryOriginalCollisions.surviving_hash_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:35.664812+00:00
-- url     : https://prove2.me/submissions/9d3c35eb-c6bd-450b-a810-f3ffbf19263c

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions

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
    Function.Injective (fun a : {a : B // a ∉ deleted hash} => hash a.val) := by
  intro a b h
  apply Subtype.ext
  by_contra hab
  apply a.property
  exact mem_filter.mpr ⟨mem_univ _,b.val,hab,h⟩
end ThreeSum.TernaryOriginalCollisions
