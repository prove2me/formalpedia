-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.not_mem_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:46.265777+00:00
-- url     : https://prove2.me/submissions/291da37f-096f-46bb-afeb-fbcfe82302dd

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_empty
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_valid_empty

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.valid_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [Hashable α] (key : α) :
    ¬ Mem key (empty : VerifiedHAMT.SetWithoutValArray.Raw α) := by
  simp [Mem, empty, mkEmptyEntries, hasKey_entries, mkEmptyEntriesArray, EntryHasKey]
end VerifiedHAMT.SetWithoutValArray.Raw
