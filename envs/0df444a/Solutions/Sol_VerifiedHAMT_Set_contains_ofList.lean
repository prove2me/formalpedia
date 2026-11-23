-- Prove2me | solution 1 for VerifiedHAMT.Set.contains_ofList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:26.141128+00:00
-- url     : https://prove2.me/submissions/165a3fb8-3999-4853-9a4a-26b96d15ca66

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Set_toMap_ofMap
public import Theorems.Thm_VerifiedHAMT_Set_ofMap_toMap
public import Theorems.Thm_VerifiedHAMT_Set_toRaw_ofRaw
public import Theorems.Thm_VerifiedHAMT_Set_ofRaw_toRaw
public import Theorems.Thm_VerifiedHAMT_Set_empty_eq_emptyc
public import Theorems.Thm_VerifiedHAMT_Set_toRaw_empty
public import Theorems.Thm_VerifiedHAMT_Set_toMap_insert
public import Theorems.Thm_VerifiedHAMT_Set_toRaw_insert
public import Theorems.Thm_VerifiedHAMT_Set_contains_eq_true_iff
public import Theorems.Thm_VerifiedHAMT_Set_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_Set_size_empty
public import Theorems.Thm_VerifiedHAMT_Set_contains_empty
public import Theorems.Thm_VerifiedHAMT_Set_contains_insert
public import Theorems.Thm_VerifiedHAMT_Set_contains_insert_self
public import Theorems.Thm_VerifiedHAMT_Set_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_Set_mem_insert_self
public import Theorems.Thm_VerifiedHAMT_Set_mem_singleton
public import Theorems.Thm_VerifiedHAMT_Set_mem_ofList
public import Theorems.Thm_VerifiedHAMT_Map_contains_empty
public import Theorems.Thm_VerifiedHAMT_Map_contains_insert
public import Theorems.Thm_VerifiedHAMT_Map_contains_insert_self
public import Theorems.Thm_VerifiedHAMT_Map_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_Map_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_Map_ofRaw_toRaw
public import Theorems.Thm_VerifiedHAMT_Map_size_empty
public import Theorems.Thm_VerifiedHAMT_Map_toRaw_empty
public import Theorems.Thm_VerifiedHAMT_Map_toRaw_insert
public import Theorems.Thm_VerifiedHAMT_Map_toRaw_ofRaw
public import Theorems.Thm_VerifiedHAMT_contains_empty
public import Theorems.Thm_VerifiedHAMT_contains_eq_true_iff
public import Theorems.Thm_VerifiedHAMT_contains_insert
public import Theorems.Thm_VerifiedHAMT_contains_insert_self
public import Theorems.Thm_VerifiedHAMT_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_not_mem_empty

attribute [local simp] VerifiedHAMT.Set.toMap_ofMap
attribute [local simp] VerifiedHAMT.Set.ofMap_toMap
attribute [local simp] VerifiedHAMT.Set.toRaw_ofRaw
attribute [local simp] VerifiedHAMT.Set.ofRaw_toRaw
attribute [local simp] VerifiedHAMT.Set.empty_eq_emptyc
attribute [local simp] VerifiedHAMT.Set.toRaw_empty
attribute [local simp] VerifiedHAMT.Set.toMap_insert
attribute [local simp] VerifiedHAMT.Set.toRaw_insert
attribute [local simp] VerifiedHAMT.Set.not_mem_empty
attribute [local simp] VerifiedHAMT.Set.size_empty
attribute [local simp] VerifiedHAMT.Set.contains_empty
attribute [local simp] VerifiedHAMT.Set.contains_insert
attribute [local simp] VerifiedHAMT.Set.contains_insert_self
attribute [local simp] VerifiedHAMT.Set.mem_insert_iff
attribute [local simp] VerifiedHAMT.Set.mem_insert_self
attribute [local simp] VerifiedHAMT.Set.mem_singleton
attribute [local simp] VerifiedHAMT.Set.mem_ofList

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (keys : List α) (key : α) :
    (ofList keys).contains key = keys.contains key := by
  apply Bool.eq_iff_iff.mpr
  simp only [contains_eq_true_iff, mem_ofList, List.contains_iff_mem]
end VerifiedHAMT.Set
