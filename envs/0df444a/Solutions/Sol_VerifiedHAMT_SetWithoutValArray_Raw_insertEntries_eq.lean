-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:44.04483+00:00
-- url     : https://prove2.me/submissions/00035407-b64b-4e64-86e3-2c8b8dae1d6b

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift branching maxDepth maxCollisions)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (h : USize) (key : α) (hi : slot h < es.size) :
    insertEntries es childInsert h key =
      es.set (slot h) (match es[slot h], Array.getElem_mem hi with
        | .null, _ => .entry key
        | .entry k, _ => if key == k then .entry key
            else .ref (mkCollisionNode k key)
        | .ref child, hmem => .ref (childInsert child hmem (nextHash h) key)) hi := by
  simp only [insertEntries, dif_pos hi]
  split <;> split <;> (try split) <;> simp_all
end VerifiedHAMT.SetWithoutValArray.Raw
