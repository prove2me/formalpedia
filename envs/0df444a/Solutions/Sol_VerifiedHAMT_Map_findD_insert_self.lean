-- Prove2me | solution 1 for VerifiedHAMT.Map.findD_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:12:35.466571+00:00
-- url     : https://prove2.me/submissions/5d704a14-923b-43e4-8401-f5f8e53fedc1

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_insert_self


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α]
    (map : Map α β) (key : α) (value fallback : β) :
    (map.insert key value).findD key fallback = value :=
  VerifiedHAMT.findD_insert_self map.toRaw map.valid map.unique key value fallback
end VerifiedHAMT.Map
