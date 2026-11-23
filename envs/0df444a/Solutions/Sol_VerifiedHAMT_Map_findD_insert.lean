-- Prove2me | solution 1 for VerifiedHAMT.Map.findD_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:12:35.11967+00:00
-- url     : https://prove2.me/submissions/52384a77-5d13-4a08-b1f8-038b134bd034

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_insert


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α]
    (map : Map α β) (key q : α) (value fallback : β) :
    (map.insert key value).findD q fallback =
      if q == key then value else map.findD q fallback :=
  VerifiedHAMT.findD_insert map.toRaw map.valid map.unique key q value fallback
end VerifiedHAMT.Map
