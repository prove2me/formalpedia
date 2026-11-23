-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.toRaw_ofRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:08:29.845798+00:00
-- url     : https://prove2.me/submissions/e5f350ac-c08f-4535-8dfd-e12ea966b6c7

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
theorem _root_.solution (raw : Raw α)
    (valid : Raw.Valid raw) (unique : Raw.Unique raw.root) :
    (ofRaw raw valid unique).toRaw = raw := rfl
end VerifiedHAMT.SetWithoutValArray
