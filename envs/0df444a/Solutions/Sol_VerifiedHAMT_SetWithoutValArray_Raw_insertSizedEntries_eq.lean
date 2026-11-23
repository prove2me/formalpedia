-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertSizedEntries_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:07.561715+00:00
-- url     : https://prove2.me/submissions/4e3986aa-aa11-427e-934a-26e71e86ee22

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollision_size_eq
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_containsNode_entries

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.insertCollision_size_eq

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth maxCollisions)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [Hashable α]
    (es : Array (Entry α (Node α))) (size : Nat)
    (childInsert : (child : Node α) → .ref child ∈ es →
      Nat → USize → α → SizedRaw α)
    (childModel : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (h : USize) (key : α)
    (childSpec : ∀ child hmem,
      childInsert child hmem size (nextHash h) key =
        ⟨⟨childModel child hmem (nextHash h) key⟩,
          if containsNode child (nextHash h) key then size else size + 1⟩) :
    insertSizedEntries es size childInsert h key =
      ⟨⟨.entries (insertEntries es childModel h key)⟩,
        if containsNode (.entries es) h key then size else size + 1⟩ := by
  simp only [insertSizedEntries, insertEntries, containsNode_entries]
  split <;> grind
end VerifiedHAMT.SetWithoutValArray.Raw
