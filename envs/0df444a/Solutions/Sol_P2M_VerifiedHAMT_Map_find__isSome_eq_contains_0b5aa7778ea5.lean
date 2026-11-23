-- Prove2me | solution 1 for P2M_VerifiedHAMT_Map_find__isSome_eq_contains_0b5aa7778ea5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:25.737547+00:00
-- url     : https://prove2.me/submissions/4bec07af-5b95-4569-b37f-92906d7732a5

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__isSome_eq_contains_a614a0a0acb2


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key : α) :
    (map.find? key).isSome = map.contains key :=
  VerifiedHAMT.find?_isSome_eq_contains map.toRaw map.valid key
end VerifiedHAMT.Map
