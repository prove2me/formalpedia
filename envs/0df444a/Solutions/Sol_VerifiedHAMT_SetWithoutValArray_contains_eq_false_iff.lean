-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.contains_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:32.634197+00:00
-- url     : https://prove2.me/submissions/555d05a5-7845-4480-a3df-ffb13f9dc346

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_false_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    set.contains key = false ↔ key ∉ set := Raw.contains_eq_false_iff set.toRaw set.valid key
end VerifiedHAMT.SetWithoutValArray
