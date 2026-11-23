-- Prove2me | solution 1 for VerifiedHAMT.Map.mem_keys
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:59:47.760004+00:00
-- url     : https://prove2.me/submissions/be475374-9f2e-4b35-9700-e8bc47f19167

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mem_keyList


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution (map : Map α β) (key : α) : key ∈ map.keys ↔ key ∈ map :=
  mem_keyList map.valid key
end VerifiedHAMT.Map
