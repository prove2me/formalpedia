-- Prove2me | solution 1 for P2M_VerifiedHAMT_find__isSome_eq_contains_a614a0a0acb2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:00.475137+00:00
-- url     : https://prove2.me/submissions/479d6cc8-67b3-4554-9b08-f0ae92d3dd50

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_VerifiedHAMT_findNode_sound
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac
public import Theorems.Thm_VerifiedHAMT_EntryHasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_contains_eq_false_iff
public import Theorems.Thm_VerifiedHAMT_contains_eq_true_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    (VerifiedHAMT.find? map key).isSome = VerifiedHAMT.contains map key := by
  cases he : VerifiedHAMT.find? map key with
  | none =>
    have hm := (find?_eq_none_iff map wf key).mp he
    simp [(contains_eq_false_iff map wf key).mpr hm]
  | some value =>
    have hm := (findNode_sound _ _ _ _ he).hasKey
    simp [(contains_eq_true_iff map wf key).mpr hm]
end VerifiedHAMT
