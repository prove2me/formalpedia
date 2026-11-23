-- Prove2me | solution 1 for VerifiedHAMT.mem_entryKeyList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:59.0398+00:00
-- url     : https://prove2.me/submissions/f44a9937-0adb-40fa-aff9-1fde646d73f9

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
public import Theorems.Thm_VerifiedHAMT_keyList_collision
attribute [local simp] VerifiedHAMT.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {key : α} {e : Entry α β (Node α β)}
    (child : ∀ c, e = .ref c → (key ∈ keyList c ↔ HasKey key c)) :
    key ∈ entryKeyList e ↔ EntryHasKey key e := by
  cases e with
  | null => simp [entryKeyList, EntryHasKey]
  | entry k v => simp [entryKeyList, EntryHasKey]
  | ref c => simpa [entryKeyList, EntryHasKey] using child c rfl
end VerifiedHAMT
