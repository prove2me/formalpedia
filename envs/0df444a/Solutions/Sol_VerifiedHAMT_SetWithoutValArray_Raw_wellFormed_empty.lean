-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:36:23.446068+00:00
-- url     : https://prove2.me/submissions/354f6d08-1009-430b-b289-a0c0e3785a98

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_mkCollisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution (hashAt : α → USize) :
    WellFormed hashAt mkEmptyEntries := by
  apply WellFormed.entries
  · simp [mkEmptyEntriesArray]
  · intro i hi key hk
    simp [mkEmptyEntriesArray, EntryHasKey] at hk
  · intro i hi child hc
    simp [mkEmptyEntriesArray] at hc
end VerifiedHAMT.SetWithoutValArray.Raw
