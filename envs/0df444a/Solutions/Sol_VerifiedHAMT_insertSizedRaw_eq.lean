-- Prove2me | solution 1 for VerifiedHAMT.insertSizedRaw_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:51.610999+00:00
-- url     : https://prove2.me/submissions/dce458fa-80a1-4192-afed-a9a37d84d423

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_InsertSized
public import Theorems.Thm_VerifiedHAMT_insertCollision_size_eq
public import Theorems.Thm_VerifiedHAMT_insertSizedEntries_eq
public import Theorems.Thm_VerifiedHAMT_insertSizedNoExpand_eq
attribute [local simp] VerifiedHAMT.insertCollision_size_eq

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α β) (h : USize) (key : α) (value : β) :
    insertSizedRaw levels offset s h key value =
      ⟨⟨insertNode levels offset s.toRaw.root h key value⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  induction levels generalizing offset s h key value with
  | zero => exact insertSizedNoExpand_eq s h key value
  | succ levels ih =>
    obtain ⟨⟨node⟩, size⟩ := s
    cases node with
    | entries es =>
      simp only [insertSizedRaw, insertNode]
      apply insertSizedEntries_eq
      intro child hmem
      exact ih (offset + shift) ⟨⟨child⟩, size⟩ (nextHash h) key value
    | collision keys vals hsz =>
      simp only [insertSizedRaw, insertNode, containsNode, insertCollision_size_eq]
      split <;> rfl
end VerifiedHAMT
