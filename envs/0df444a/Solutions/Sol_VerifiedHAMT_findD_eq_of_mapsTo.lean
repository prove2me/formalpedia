-- Prove2me | solution 1 for VerifiedHAMT.findD_eq_of_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:57:47.255544+00:00
-- url     : https://prove2.me/submissions/ce2a7fa4-95bb-43f0-bcc1-72cb2343848a

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba
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
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value fallback : β) (hb : MapsTo key value map) :
    findD map key fallback = value := by
  simp only [findD, (find?_eq_some_iff map wf hu key value).mpr hb, Option.getD_some]
end VerifiedHAMT
