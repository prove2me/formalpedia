-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.mem_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:22.237677+00:00
-- url     : https://prove2.me/submissions/8f2ce102-a05d-4aa7-9329-97e4891bbc30

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_insert_iff

attribute [local simp] VerifiedHAMT.SetWithoutValArray.mem_insert_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    key ∈ set.insert key := (mem_insert_iff set key key).mpr (Or.inl rfl)
end VerifiedHAMT.SetWithoutValArray
