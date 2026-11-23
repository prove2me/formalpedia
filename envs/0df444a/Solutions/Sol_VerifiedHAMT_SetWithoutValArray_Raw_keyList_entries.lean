-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.keyList_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:48:23.200056+00:00
-- url     : https://prove2.me/submissions/630a6e6b-5f3d-4739-b2d6-ba19ec02c1dd

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_entryListKeyList_eq_flatMap

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution (es : Array (Entry α (Node α))) :
    keyList (.entries es) = es.toList.flatMap entryKeyList := by
  cases es with
  | mk es => simp [keyList, entriesKeyList, entryListKeyList_eq_flatMap]
end VerifiedHAMT.SetWithoutValArray.Raw
