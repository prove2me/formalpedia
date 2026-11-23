-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.contains_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:21.782244+00:00
-- url     : https://prove2.me/submissions/7fa4122b-74a2-4a56-b463-92ab6f89ae1c

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_insert_self


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).contains key = true := Raw.contains_insert_self set.toRaw set.valid key
end VerifiedHAMT.SetWithoutValArray
