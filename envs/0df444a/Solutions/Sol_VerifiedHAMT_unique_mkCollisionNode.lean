-- Prove2me | solution 1 for VerifiedHAMT.unique_mkCollisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:18.875525+00:00
-- url     : https://prove2.me/submissions/225888d4-3fdb-458d-88ed-309275ed6392

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
theorem _root_.solution {k₁ k₂ : α} (hne : k₁ ≠ k₂) (v₁ v₂ : β) :
    Unique (mkCollisionNode k₁ v₁ k₂ v₂) := by
  apply Unique.collision
  intro i hi j hj
  have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
  have hj' : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp_all [Ne.symm hne]
end VerifiedHAMT
