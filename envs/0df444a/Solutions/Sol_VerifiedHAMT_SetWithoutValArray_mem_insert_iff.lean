-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.mem_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:07:47.040372+00:00
-- url     : https://prove2.me/submissions/face5b82-217f-43a3-9cff-664db086e1ed

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_insert_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (set : SetWithoutValArray α) (key q : α) :
    q ∈ set.insert key ↔ q = key ∨ q ∈ set := Raw.mem_insert_iff set.toRaw set.valid key q
end VerifiedHAMT.SetWithoutValArray
