-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.keyCount_empty_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:09.195028+00:00
-- url     : https://prove2.me/submissions/323ed4af-6e5d-46b3-af78-c5f1390708c4

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_entries
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_collision
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [Hashable α] :
    keyCount (empty : Raw α).root = 0 := by
  simp [keyCount, empty, mkEmptyEntries, mkEmptyEntriesArray, keyList_entries,
    List.flatMap_replicate, entryKeyList]
end VerifiedHAMT.SetWithoutValArray.Raw
