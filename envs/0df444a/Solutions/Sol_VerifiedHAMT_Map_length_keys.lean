-- Prove2me | solution 1 for VerifiedHAMT.Map.length_keys
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:59:52.021575+00:00
-- url     : https://prove2.me/submissions/641ced30-5e46-4ad2-a2cf-d14fae901745

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution (map : Map α β) : map.keys.length = map.size :=
  map.size_eq.symm
end VerifiedHAMT.Map
