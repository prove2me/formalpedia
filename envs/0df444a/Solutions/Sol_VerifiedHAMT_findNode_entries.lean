-- Prove2me | solution 1 for VerifiedHAMT.findNode_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:21.257535+00:00
-- url     : https://prove2.me/submissions/b849e036-0f89-41f7-ac20-886258a48b80

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] (es : Array (Entry α β (Node α β)))
    (hash : USize) (key : α) :
    findNode (.entries es) hash key =
      if hi : slot hash < es.size then
        match es[slot hash] with
        | .null => none
        | .entry key' value => if key == key' then some value else none
        | .ref child => findNode child (nextHash hash) key
      else none := by
  rw [findNode]
  split
  · split <;> simp_all
  · rfl
end VerifiedHAMT
