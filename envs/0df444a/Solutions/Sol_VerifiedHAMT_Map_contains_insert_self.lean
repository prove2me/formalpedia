-- Prove2me | solution 1 for VerifiedHAMT.Map.contains_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:16.645726+00:00
-- url     : https://prove2.me/submissions/60f1647b-e7a6-42a9-bdcb-92edaa9048cc

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_contains_insert_self


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).contains key = true :=
  VerifiedHAMT.contains_insert_self map.toRaw map.valid key value
end VerifiedHAMT.Map
