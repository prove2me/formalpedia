-- Prove2me | solution 1 for VerifiedHAMT.Map.mem_iff_exists_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:48.520217+00:00
-- url     : https://prove2.me/submissions/b93c9133-e458-434b-89fc-bce738474bff

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_hasKey_iff_exists_binding


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution (map : Map α β) (key : α) :
    key ∈ map ↔ ∃ value, map.MapsTo key value :=
  hasKey_iff_exists_binding
end VerifiedHAMT.Map
