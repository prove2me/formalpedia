-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.contains_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:51:18.314417+00:00
-- url     : https://prove2.me/submissions/a4fe2e0b-4f72-4e19-86c7-f2e9ce623cbc

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_insert
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_true_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key q : α) :
    contains (insert map key) q = ((q == key) || contains map q) := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_true_iff _ (valid_insert map wf key), mem_insert_iff map wf]
  simp [contains_eq_true_iff map wf]
end VerifiedHAMT.SetWithoutValArray.Raw
