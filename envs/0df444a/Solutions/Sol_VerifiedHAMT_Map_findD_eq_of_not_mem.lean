-- Prove2me | solution 1 for VerifiedHAMT.Map.findD_eq_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:45.848406+00:00
-- url     : https://prove2.me/submissions/42e2ddde-f976-47b3-8fc4-643843f5fb6d

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_eq_of_not_mem


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β)
    (key : α) (fallback : β) (hm : key ∉ map) : map.findD key fallback = fallback :=
  VerifiedHAMT.findD_eq_of_not_mem map.toRaw map.valid key fallback hm
end VerifiedHAMT.Map
