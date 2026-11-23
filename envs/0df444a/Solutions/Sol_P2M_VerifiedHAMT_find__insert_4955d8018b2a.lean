-- Prove2me | solution 1 for P2M_VerifiedHAMT_find__insert_4955d8018b2a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:12.104634+00:00
-- url     : https://prove2.me/submissions/6f2a212b-6db2-480f-9614-dc1472d7551d

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba
public import Theorems.Thm_P2M_VerifiedHAMT_find__empty_a79d102e4768
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_iff
public import Theorems.Thm_VerifiedHAMT_unique_insert
public import Theorems.Thm_VerifiedHAMT_valid_insert

attribute [local simp] VerifiedHAMT.find?_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value : β) :
    VerifiedHAMT.find? (VerifiedHAMT.insert map key value) q = if q == key then some value else VerifiedHAMT.find? map q := by
  apply Option.ext
  intro w
  rw [find?_eq_some_iff _ (valid_insert map wf key value) (unique_insert map wf hu key value),
    mapsTo_insert_iff map wf hu key q value w]
  by_cases h : q = key
  · simp [h, eq_comm]
  · simp [h, find?_eq_some_iff map wf hu q w]
end VerifiedHAMT
