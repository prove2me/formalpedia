-- Prove2me | solution 1 for VerifiedHAMT.containsNode_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:06.761454+00:00
-- url     : https://prove2.me/submissions/13c2fcd6-d05a-48f2-81cb-d22a34e7ced2

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] (es : Array (Entry α β (Node α β)))
    (hash : USize) (key : α) :
    containsNode (.entries es) hash key =
      if hi : slot hash < es.size then
        match es[slot hash] with
        | .null => false
        | .entry key' _ => key == key'
        | .ref child => containsNode child (nextHash hash) key
      else false := by
  rw [containsNode]
  split
  · split <;> simp_all
  · rfl
end VerifiedHAMT
