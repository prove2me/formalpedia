-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.toRaw_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:09:28.613256+00:00
-- url     : https://prove2.me/submissions/a9c3ec59-a048-4991-b3d4-d3f91709cc7a

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
theorem _root_.solution : (∅ : SetWithoutValArray α).toRaw = Raw.empty := rfl
end VerifiedHAMT.SetWithoutValArray
