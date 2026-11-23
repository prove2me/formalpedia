-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.contains_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:09:40.524744+00:00
-- url     : https://prove2.me/submissions/f591cbc3-85f1-472f-94a8-48d3c40e478e

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (key : α) :
    (∅ : SetWithoutValArray α).contains key = false := Raw.contains_empty key
end VerifiedHAMT.SetWithoutValArray
