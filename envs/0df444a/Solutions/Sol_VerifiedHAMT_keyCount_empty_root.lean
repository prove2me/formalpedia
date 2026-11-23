-- Prove2me | solution 1 for VerifiedHAMT.keyCount_empty_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:12.013917+00:00
-- url     : https://prove2.me/submissions/dcac5b53-2ded-4bb5-83e1-28a5f7bc8bba

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
public import Theorems.Thm_VerifiedHAMT_keyList_entries
public import Theorems.Thm_VerifiedHAMT_keyList_collision
attribute [local simp] VerifiedHAMT.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [Hashable α] :
    keyCount (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β).root = 0 := by
  simp [keyCount, Lean.PersistentHashMap.empty, mkEmptyEntriesArray, keyList_entries,
    List.flatMap_replicate, entryKeyList]
end VerifiedHAMT
