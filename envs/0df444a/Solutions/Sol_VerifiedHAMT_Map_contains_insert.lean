-- Prove2me | solution 1 for VerifiedHAMT.Map.contains_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:15.746851+00:00
-- url     : https://prove2.me/submissions/6b5a2eb9-471c-482d-b144-0790d7db9f85

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_contains_insert


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key q : α) (value : β) :
    (map.insert key value).contains q = ((q == key) || map.contains q) :=
  VerifiedHAMT.contains_insert map.toRaw map.valid key q value
end VerifiedHAMT.Map
