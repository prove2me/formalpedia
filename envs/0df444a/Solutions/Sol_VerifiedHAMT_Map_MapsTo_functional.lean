-- Prove2me | solution 1 for VerifiedHAMT.Map.MapsTo.functional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:04:19.121205+00:00
-- url     : https://prove2.me/submissions/ff22bc89-1c87-45d0-9431-d5f20b9007f1

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_HasBinding_functional


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
namespace MapsTo
theorem _root_.solution {map : Map α β} {key : α} {v w : β}
    (hv : map.MapsTo key v) (hw : map.MapsTo key w) : v = w :=
  HasBinding.functional map.valid map.unique hv hw
end MapsTo
end VerifiedHAMT.Map
