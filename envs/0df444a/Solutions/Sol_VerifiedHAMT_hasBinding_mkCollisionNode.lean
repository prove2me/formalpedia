-- Prove2me | solution 1 for VerifiedHAMT.hasBinding_mkCollisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:52.197072+00:00
-- url     : https://prove2.me/submissions/9e24e8ac-5e03-4099-bb5f-81bc868373ba

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
attribute [local simp] VerifiedHAMT.hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.slot_zero
attribute [local simp] VerifiedHAMT.valid_empty
attribute [local simp] VerifiedHAMT.not_mem_empty
attribute [local simp] VerifiedHAMT.hasBinding_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution (k₁ k₂ q : α) (v₁ v₂ w : β) :
    HasBinding q w (mkCollisionNode k₁ v₁ k₂ v₂) ↔
      (q = k₁ ∧ w = v₁) ∨ (q = k₂ ∧ w = v₂) := by
  simp only [mkCollisionNode, hasBinding_collision, Array.size_push, Array.mkEmpty, Array.size_empty]
  constructor
  · grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exists 0 ; grind
    · exists 1 ; grind
end VerifiedHAMT
