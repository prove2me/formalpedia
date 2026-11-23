-- Prove2me | solution 1 for P2M_VerifiedHAMT_Map_find__eq_some_iff_80d7561a98c5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:16.657517+00:00
-- url     : https://prove2.me/submissions/75fb14b2-a1f2-4637-9556-1f6d37013340

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    map.find? key = some value ↔ map.MapsTo key value :=
  VerifiedHAMT.find?_eq_some_iff map.toRaw map.valid map.unique key value
end VerifiedHAMT.Map
