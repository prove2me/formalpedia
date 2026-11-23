-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.not_mem_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:09:31.195004+00:00
-- url     : https://prove2.me/submissions/b1df0858-0509-483b-8563-813581d4e480

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution (key : α) : key ∉ (∅ : SetWithoutValArray α) :=
  Raw.not_mem_empty key
end VerifiedHAMT.SetWithoutValArray
