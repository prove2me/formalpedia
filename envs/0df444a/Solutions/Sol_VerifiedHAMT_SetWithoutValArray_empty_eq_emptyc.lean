-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.empty_eq_emptyc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:09:25.654985+00:00
-- url     : https://prove2.me/submissions/42f193b3-19ed-4419-952d-dea51a525efe

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
theorem _root_.solution : (empty : SetWithoutValArray α) = ∅ := rfl
end VerifiedHAMT.SetWithoutValArray
