-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.ofRaw_toRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:08:32.592526+00:00
-- url     : https://prove2.me/submissions/0d71ca5c-3d98-4c5f-8502-780534d64971

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution (set : SetWithoutValArray α) :
    ofRaw set.toRaw set.valid set.unique = set := by
  cases set with
  | mk data valid unique size_eq =>
    cases data with
    | mk raw size =>
      change size = Raw.keyCount raw.root at size_eq
      subst size
      rfl
end VerifiedHAMT.SetWithoutValArray
