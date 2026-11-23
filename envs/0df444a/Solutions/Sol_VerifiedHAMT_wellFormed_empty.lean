-- Prove2me | solution 1 for VerifiedHAMT.wellFormed_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:37.225392+00:00
-- url     : https://prove2.me/submissions/889d85f9-7199-415d-a9aa-2a58abcb16b6

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_slot_zero
attribute [local simp] VerifiedHAMT.hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.slot_zero

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution (hashAt : α → USize) :
    WellFormed (β := β) hashAt mkEmptyEntries := by
  apply WellFormed.entries
  · simp [mkEmptyEntriesArray]
  · intro i hi key hk
    simp [mkEmptyEntriesArray, EntryHasKey] at hk
  · intro i hi child hc
    simp [mkEmptyEntriesArray] at hc
end VerifiedHAMT
