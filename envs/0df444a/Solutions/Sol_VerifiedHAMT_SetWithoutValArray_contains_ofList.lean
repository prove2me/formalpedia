-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.contains_ofList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:17:21.895322+00:00
-- url     : https://prove2.me/submissions/18346beb-bdfc-461b-9cb8-c878e4099b5b

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_toRaw_ofRaw
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_ofRaw_toRaw
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_size_ofRaw
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_empty_eq_emptyc
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_toRaw_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_toRaw_insert
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_size_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_contains_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_contains_insert
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_contains_insert_self
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_insert_self
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_singleton
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_ofList
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_true_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_insert
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_insert_self
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty

attribute [local simp] VerifiedHAMT.SetWithoutValArray.toRaw_ofRaw
attribute [local simp] VerifiedHAMT.SetWithoutValArray.ofRaw_toRaw
attribute [local simp] VerifiedHAMT.SetWithoutValArray.size_ofRaw
attribute [local simp] VerifiedHAMT.SetWithoutValArray.empty_eq_emptyc
attribute [local simp] VerifiedHAMT.SetWithoutValArray.toRaw_empty
attribute [local simp] VerifiedHAMT.SetWithoutValArray.toRaw_insert
attribute [local simp] VerifiedHAMT.SetWithoutValArray.not_mem_empty
attribute [local simp] VerifiedHAMT.SetWithoutValArray.size_empty
attribute [local simp] VerifiedHAMT.SetWithoutValArray.contains_empty
attribute [local simp] VerifiedHAMT.SetWithoutValArray.contains_insert
attribute [local simp] VerifiedHAMT.SetWithoutValArray.contains_insert_self
attribute [local simp] VerifiedHAMT.SetWithoutValArray.mem_insert_iff
attribute [local simp] VerifiedHAMT.SetWithoutValArray.mem_insert_self
attribute [local simp] VerifiedHAMT.SetWithoutValArray.mem_singleton
attribute [local simp] VerifiedHAMT.SetWithoutValArray.mem_ofList

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (keys : List α) (key : α) :
    (ofList keys).contains key = keys.contains key := by
  apply Bool.eq_iff_iff.mpr
  simp only [contains_eq_true_iff, mem_ofList, List.contains_iff_mem]
end VerifiedHAMT.SetWithoutValArray
