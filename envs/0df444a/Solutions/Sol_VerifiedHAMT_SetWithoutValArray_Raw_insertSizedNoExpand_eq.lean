-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertSizedNoExpand_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:51:47.978286+00:00
-- url     : https://prove2.me/submissions/8e158832-4dfb-4ef1-9531-835bf49cbdee

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollision_size_eq
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertSizedEntries_eq
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.insertCollision_size_eq

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth maxCollisions)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [Hashable α] (s : SizedRaw α) (h : USize)
    (key : α) :
    insertSizedNoExpand s h key =
      ⟨⟨insertNoExpand s.toRaw.root h key⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  obtain ⟨⟨node⟩, size⟩ := s
  cases node with
  | collision keys =>
    simp only [insertSizedNoExpand.eq_def, insertNoExpand.eq_def, containsNode,
      ← insertCollision.eq_def, insertCollision_size_eq]
  | entries es =>
    rw [insertSizedNoExpand.eq_def, insertNoExpand.eq_def]
    apply insertSizedEntries_eq
    intro child hmem
    exact solution ⟨⟨child⟩, size⟩ (nextHash h) key
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_lt_of_mem hmem
  simp at hs ⊢
  omega
end VerifiedHAMT.SetWithoutValArray.Raw
