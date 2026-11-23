-- Prove2me | solution 1 for VerifiedHAMT.Map.mapsTo_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:12:39.443126+00:00
-- url     : https://prove2.me/submissions/f9a775cc-c899-4c9d-a532-188cda1a6681

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α]
    (map : Map α β) (key q : α) (value w : β) :
    (map.insert key value).MapsTo q w ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ map.MapsTo q w) :=
  VerifiedHAMT.mapsTo_insert_iff map.toRaw map.valid map.unique key q value w
end VerifiedHAMT.Map
