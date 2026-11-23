-- Prove2me | solution 1 for VerifiedHAMT.insertSizedEntries_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:43.465162+00:00
-- url     : https://prove2.me/submissions/acfdbd8d-e681-4f6c-87df-704232697784

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_InsertSized
public import Theorems.Thm_VerifiedHAMT_insertCollision_size_eq
public import Theorems.Thm_VerifiedHAMT_containsNode_entries

attribute [local simp] VerifiedHAMT.insertCollision_size_eq

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [Hashable α]
    (es : Array (Entry α β (Node α β))) (size : Nat)
    (childInsert : (child : Node α β) → .ref child ∈ es →
      Nat → USize → α → β → SizedRaw α β)
    (childModel : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (h : USize) (key : α) (value : β)
    (childSpec : ∀ child hmem,
      childInsert child hmem size (nextHash h) key value =
        ⟨⟨childModel child hmem (nextHash h) key value⟩,
          if containsNode child (nextHash h) key then size else size + 1⟩) :
    insertSizedEntries es size childInsert h key value =
      ⟨⟨.entries (insertEntries es childModel h key value)⟩,
        if containsNode (.entries es) h key then size else size + 1⟩ := by
  simp only [insertSizedEntries, insertEntries, containsNode_entries]
  split <;> grind
end VerifiedHAMT
