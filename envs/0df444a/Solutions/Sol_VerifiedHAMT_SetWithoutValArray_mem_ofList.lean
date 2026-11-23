-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.mem_ofList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:16:06.042843+00:00
-- url     : https://prove2.me/submissions/244462b0-69bd-4a4a-8271-4a13dff010d5

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
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_mem_foldl_insert
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_empty
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

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (keys : List α) (key : α) :
    key ∈ ofList keys ↔ key ∈ keys := by simp [ofList, mem_foldl_insert, not_mem_empty]
end VerifiedHAMT.SetWithoutValArray
