-- Prove2me | solution 1 for VerifiedHAMT.Map.toRaw_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:31.081331+00:00
-- url     : https://prove2.me/submissions/caefe138-b485-47ed-89f4-03a0fe6e3237

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
theorem _root_.solution : (∅ : Map α β).toRaw = Lean.PersistentHashMap.empty := rfl
end VerifiedHAMT.Map
