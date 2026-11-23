-- Prove2me | solution 1 for VerifiedHAMT.Map.contains_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:58:34.542906+00:00
-- url     : https://prove2.me/submissions/0ea00fcf-efcc-4d21-995e-0647c733a2ac

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_contains_eq_false_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key : α) :
    map.contains key = false ↔ key ∉ map :=
  VerifiedHAMT.contains_eq_false_iff map.toRaw map.valid key
end VerifiedHAMT.Map
