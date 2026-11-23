-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:57.890272+00:00
-- url     : https://prove2.me/submissions/d215d9be-cefd-448a-9de6-510f4376647a

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_WellFormed_slot_lt
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_eq
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_set
public import Theorems.Thm_VerifiedHAMT_WellFormed_slot_lt
public import Theorems.Thm_VerifiedHAMT_unique_mkCollisionNode


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (key : α) (wf : WellFormed hashAt (.entries es)) (hu : Unique (.entries es))
    (childSpec : ∀ (child : Node α) (hmem : .ref child ∈ es), Unique child →
      Unique (childInsert child hmem (nextHash (hashAt key)) key)) :
    Unique (.entries (insertEntries es childInsert (hashAt key) key)) := by
  have hi := wf.slot_lt (hashAt key)
  rw [insertEntries_eq _ _ _ _ hi]
  split
  · apply unique_set hu <;> grind
  · split <;> apply unique_set hu <;> grind [unique_mkCollisionNode]
  · rename_i child hmem he _
    have hchild : Unique child := by cases hu <;> grind
    apply unique_set hu <;> grind
end VerifiedHAMT.SetWithoutValArray.Raw
