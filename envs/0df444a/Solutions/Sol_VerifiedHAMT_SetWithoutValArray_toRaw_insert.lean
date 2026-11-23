-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.toRaw_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:09:29.164007+00:00
-- url     : https://prove2.me/submissions/04255c1e-4ea5-4463-8cfa-dfaf99ce6a47

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
theorem _root_.solution [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).toRaw = Raw.insert set.toRaw key := rfl
end VerifiedHAMT.SetWithoutValArray
