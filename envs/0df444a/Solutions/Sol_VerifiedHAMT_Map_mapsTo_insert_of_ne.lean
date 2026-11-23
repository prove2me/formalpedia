-- Prove2me | solution 1 for VerifiedHAMT.Map.mapsTo_insert_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:12:43.654801+00:00
-- url     : https://prove2.me/submissions/85a3547b-26f1-4152-8a4b-c0ac4344a68d

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_of_ne


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α]
    (map : Map α β) (key q : α) (value w : β) (hne : q ≠ key) :
    (map.insert key value).MapsTo q w ↔ map.MapsTo q w :=
  VerifiedHAMT.mapsTo_insert_of_ne map.toRaw map.valid map.unique key q value w hne
end VerifiedHAMT.Map
