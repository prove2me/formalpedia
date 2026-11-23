-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.size_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:46.498468+00:00
-- url     : https://prove2.me/submissions/c030a6b6-b9e0-417e-806e-034c7389ee2a

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_true_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).size = if key ∈ set then set.size else set.size + 1 := by
  change (if set.contains key then set.size else set.size + 1) = _
  by_cases h : key ∈ set
  · rw [if_pos ((contains_eq_true_iff set key).mpr h), if_pos h]
  · rw [if_neg (mt (contains_eq_true_iff set key).mp h), if_neg h]
end VerifiedHAMT.SetWithoutValArray
