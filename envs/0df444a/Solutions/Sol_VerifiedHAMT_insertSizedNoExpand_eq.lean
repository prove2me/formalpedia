-- Prove2me | solution 1 for VerifiedHAMT.insertSizedNoExpand_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:40.398261+00:00
-- url     : https://prove2.me/submissions/c20d254a-0bbf-4eb3-8306-1d92c7a68e30

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_InsertSized
public import Theorems.Thm_VerifiedHAMT_insertCollision_size_eq
public import Theorems.Thm_VerifiedHAMT_insertSizedEntries_eq
attribute [local simp] VerifiedHAMT.insertCollision_size_eq

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [Hashable α] (s : SizedRaw α β) (h : USize)
    (key : α) (value : β) :
    insertSizedNoExpand s h key value =
      ⟨⟨insertNoExpand s.toRaw.root h key value⟩,
        if containsNode s.toRaw.root h key then s.size else s.size + 1⟩ := by
  obtain ⟨⟨node⟩, size⟩ := s
  cases node with
  | collision keys vals hsz =>
    simp only [insertSizedNoExpand.eq_def, insertNoExpand.eq_def, containsNode,
      ← insertCollision.eq_def, insertCollision_size_eq]
  | entries es =>
    rw [insertSizedNoExpand.eq_def, insertNoExpand.eq_def]
    apply insertSizedEntries_eq
    intro child hmem
    exact solution ⟨⟨child⟩, size⟩ (nextHash h) key value
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_lt_of_mem hmem
  simp at hs ⊢
  omega
end VerifiedHAMT
