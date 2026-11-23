-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.size_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:09:32.009797+00:00
-- url     : https://prove2.me/submissions/7458a73f-cd33-4f63-b48c-078b782cfc9b

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
theorem _root_.solution : (∅ : SetWithoutValArray α).size = 0 := rfl
end VerifiedHAMT.SetWithoutValArray
