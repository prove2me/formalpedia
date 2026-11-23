-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.entryListKeyList_eq_flatMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:54.502719+00:00
-- url     : https://prove2.me/submissions/ec82cddc-7d58-402a-9865-48265f2a238c

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution (es : List (Entry α (Node α))) :
    entryListKeyList es = es.flatMap entryKeyList := by
  induction es with
  | nil => simp [entryListKeyList]
  | cons e es ih => simp [entryListKeyList, ih]
end VerifiedHAMT.SetWithoutValArray.Raw
