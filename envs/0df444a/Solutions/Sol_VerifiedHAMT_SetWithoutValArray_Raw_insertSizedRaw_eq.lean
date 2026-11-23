-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertSizedRaw_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:10.615128+00:00
-- url     : https://prove2.me/submissions/772c1646-b13c-4b79-9531-8d4581c7a369

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollision_size_eq
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertSizedEntries_eq
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertSizedNoExpand_eq
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.insertCollision_size_eq

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth maxCollisions)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α) (h : USize) (key : α) :
    insertSizedRaw levels offset s h key =
      ⟨⟨insertNode levels offset s.toRaw.root h key⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  induction levels generalizing offset s h key with
  | zero => exact insertSizedNoExpand_eq s h key
  | succ levels ih =>
    obtain ⟨⟨node⟩, size⟩ := s
    cases node with
    | entries es =>
      simp only [insertSizedRaw, insertNode]
      apply insertSizedEntries_eq
      intro child hmem
      exact ih (offset + shift) ⟨⟨child⟩, size⟩ (nextHash h) key
    | collision keys =>
      simp only [insertSizedRaw, insertNode, containsNode, insertCollision_size_eq]
      split <;> rfl
end VerifiedHAMT.SetWithoutValArray.Raw
