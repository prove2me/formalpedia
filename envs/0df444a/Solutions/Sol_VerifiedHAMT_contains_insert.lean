-- Prove2me | solution 1 for VerifiedHAMT.contains_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:00.96711+00:00
-- url     : https://prove2.me/submissions/a17063c2-5d57-4f68-87d3-6e0c7d7cc0aa

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_valid_insert
public import Theorems.Thm_VerifiedHAMT_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_self
public import Theorems.Thm_VerifiedHAMT_contains_eq_true_iff

attribute [local simp] VerifiedHAMT.mapsTo_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key q : α) (value : β) :
    contains (insert map key value) q = ((q == key) || contains map q) := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_true_iff _ (valid_insert map wf key value), mem_insert_iff map wf]
  simp [contains_eq_true_iff map wf]
end VerifiedHAMT
