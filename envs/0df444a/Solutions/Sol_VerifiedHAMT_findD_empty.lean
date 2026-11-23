-- Prove2me | solution 1 for VerifiedHAMT.findD_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:55:56.870419+00:00
-- url     : https://prove2.me/submissions/be364747-8a32-47ba-85bb-ae67fe8c930c

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_P2M_VerifiedHAMT_find__empty_a79d102e4768
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_4955d8018b2a
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_self_b1de16f2743e
attribute [local simp] VerifiedHAMT.find?_empty
attribute [local simp] VerifiedHAMT.find?_insert
attribute [local simp] VerifiedHAMT.find?_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (key : α) (fallback : β) :
    findD (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key fallback = fallback := by
  simp [findD, find?_empty]
end VerifiedHAMT
