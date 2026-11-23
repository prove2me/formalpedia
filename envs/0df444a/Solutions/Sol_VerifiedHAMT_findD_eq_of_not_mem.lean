-- Prove2me | solution 1 for VerifiedHAMT.findD_eq_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:57:54.732524+00:00
-- url     : https://prove2.me/submissions/5c4c7c05-20b9-4996-b49e-86cdbf25c4bb

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac
public import Theorems.Thm_P2M_VerifiedHAMT_find__empty_a79d102e4768
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_4955d8018b2a
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_self_b1de16f2743e
attribute [local simp] VerifiedHAMT.find?_empty
attribute [local simp] VerifiedHAMT.find?_insert
attribute [local simp] VerifiedHAMT.find?_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map)
    (key : α) (fallback : β) (hm : ¬ Mem key map) :
    findD map key fallback = fallback := by
  simp only [findD, (find?_eq_none_iff map wf key).mpr hm, Option.getD_none]
end VerifiedHAMT
