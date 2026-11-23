-- Prove2me | solution 1 for VerifiedHAMT.unique_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:17.365698+00:00
-- url     : https://prove2.me/submissions/1e7affa6-761b-4904-b607-4196287ca52b

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_slot_zero
public import Theorems.Thm_VerifiedHAMT_valid_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_hasBinding_collision
public import Theorems.Thm_VerifiedHAMT_hasBinding_mkCollisionNode
attribute [local simp] VerifiedHAMT.hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.slot_zero
attribute [local simp] VerifiedHAMT.valid_empty
attribute [local simp] VerifiedHAMT.not_mem_empty
attribute [local simp] VerifiedHAMT.hasBinding_collision
attribute [local simp] VerifiedHAMT.hasBinding_mkCollisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution : Unique (mkEmptyEntries : Node α β) := by
  apply Unique.entries
  intro i hi child hc
  simp [mkEmptyEntriesArray] at hc
end VerifiedHAMT
