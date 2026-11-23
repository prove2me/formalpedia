-- Prove2me | solution 1 for VerifiedHAMT.Map.mapsTo_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:12:41.020873+00:00
-- url     : https://prove2.me/submissions/d56700d2-01d4-4187-a0d3-c0dfe375038d

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_self


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α]
    (map : Map α β) (key : α) (value w : β) :
    (map.insert key value).MapsTo key w ↔ w = value :=
  VerifiedHAMT.mapsTo_insert_self map.toRaw map.valid map.unique key value w
end VerifiedHAMT.Map
