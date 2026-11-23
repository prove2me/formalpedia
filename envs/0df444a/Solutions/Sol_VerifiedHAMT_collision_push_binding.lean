-- Prove2me | solution 1 for VerifiedHAMT.collision_push_binding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:19.531824+00:00
-- url     : https://prove2.me/submissions/deebfb11-a9da-4bd0-b4c2-def51f90c1f2

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
theorem _root_.solution (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size) (key q : α) (value w : β) :
    HasBinding q w (.collision (keys.push key) (vals.push value) (by simp [hsz])) ↔
      (q = key ∧ w = value) ∨ HasBinding q w (.collision keys vals hsz) := by
  simp only [hasBinding_collision, Array.size_push, Array.getElem_push]
  constructor
  · grind
  · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hk, hv⟩)
    · exists keys.size ; grind
    · grind
end VerifiedHAMT
