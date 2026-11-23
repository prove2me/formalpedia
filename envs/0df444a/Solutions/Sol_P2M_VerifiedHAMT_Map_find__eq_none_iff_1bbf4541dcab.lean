-- Prove2me | solution 1 for P2M_VerifiedHAMT_Map_find__eq_none_iff_1bbf4541dcab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:20.608535+00:00
-- url     : https://prove2.me/submissions/5b7990da-4372-482c-84b4-0cbb61ddcfcf

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key : α) :
    map.find? key = none ↔ key ∉ map :=
  VerifiedHAMT.find?_eq_none_iff map.toRaw map.valid key
end VerifiedHAMT.Map
