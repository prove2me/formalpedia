-- Prove2me | solution 1 for P2M_VerifiedHAMT_Map_find__insert_cd8cc38688c5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:05:36.046795+00:00
-- url     : https://prove2.me/submissions/3089ac39-f149-4751-bf46-7b8f379a4cb9

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_4955d8018b2a


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α]
    (map : Map α β) (key q : α) (value : β) :
    (map.insert key value).find? q = if q == key then some value else map.find? q :=
  VerifiedHAMT.find?_insert map.toRaw map.valid map.unique key q value
end VerifiedHAMT.Map
