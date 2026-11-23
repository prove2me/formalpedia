-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.size_ofRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:09:21.37885+00:00
-- url     : https://prove2.me/submissions/41e5f6d0-801a-4ec7-83db-9aef0c768fec

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
    (ofRaw raw valid unique).size = Raw.keyCount raw.root := rfl
end VerifiedHAMT.SetWithoutValArray
