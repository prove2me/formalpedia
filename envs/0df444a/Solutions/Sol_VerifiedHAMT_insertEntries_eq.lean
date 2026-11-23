-- Prove2me | solution 1 for VerifiedHAMT.insertEntries_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:36:40.068938+00:00
-- url     : https://prove2.me/submissions/7ead2e6e-f6f5-49a2-9e1f-5312f72ada45

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_Bindings
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] (es : Array (Entry α β (Node α β)))
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (h : USize) (key : α) (value : β) (hi : slot h < es.size) :
    insertEntries es childInsert h key value =
      es.set (slot h) (match es[slot h], Array.getElem_mem hi with
        | .null, _ => .entry key value
        | .entry k v, _ => if key == k then .entry key value
            else .ref (mkCollisionNode k v key value)
        | .ref child, hmem => .ref (childInsert child hmem (nextHash h) key value)) hi := by
  simp only [insertEntries, dif_pos hi]
  split <;> split <;> (try split) <;> simp_all
end VerifiedHAMT
