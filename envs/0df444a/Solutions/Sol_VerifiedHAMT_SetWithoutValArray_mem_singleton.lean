-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.mem_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:12:46.739964+00:00
-- url     : https://prove2.me/submissions/56645cb7-5f5c-4049-8c57-aac0f4c1fd88

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

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (key q : α) :
    q ∈ ({key} : SetWithoutValArray α) ↔ q = key := by
  change q ∈ (∅ : SetWithoutValArray α).insert key ↔ q = key
  simp [mem_insert_iff, not_mem_empty]
end VerifiedHAMT.SetWithoutValArray
