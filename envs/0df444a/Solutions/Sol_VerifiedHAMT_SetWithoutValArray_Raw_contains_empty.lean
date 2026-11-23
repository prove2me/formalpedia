-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.contains_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:52:02.082626+00:00
-- url     : https://prove2.me/submissions/7242f809-62f0-4f91-a402-2322168ff01f

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_false_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_valid_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α] (key : α) :
    contains (empty : Raw α) key = false :=
  (contains_eq_false_iff _ valid_empty key).mpr (not_mem_empty key)
end VerifiedHAMT.SetWithoutValArray.Raw
