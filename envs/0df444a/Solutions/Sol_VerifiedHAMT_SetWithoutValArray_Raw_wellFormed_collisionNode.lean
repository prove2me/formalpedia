-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_collisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:53.911186+00:00
-- url     : https://prove2.me/submissions/a9cc6e0c-387b-406f-812a-fb6c0782a16b

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution (hashAt : α → USize) (b : CollisionNode α) :
    WellFormed hashAt b.val := by
  obtain ⟨node, hb⟩ := b
  cases hb
  exact .collision _ _
end VerifiedHAMT.SetWithoutValArray.Raw
