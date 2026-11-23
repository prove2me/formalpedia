-- Prove2me | solution 1 for VerifiedHAMT.Map.size_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:59:16.061529+00:00
-- url     : https://prove2.me/submissions/ff59545c-ec45-4e93-a88c-4f292056fe41

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_contains_eq_true_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).size = if key ∈ map then map.size else map.size + 1 := by
  change (if map.contains key then map.size else map.size + 1) = _
  by_cases h : key ∈ map
  · rw [if_pos ((contains_eq_true_iff map key).mpr h), if_pos h]
  · rw [if_neg (mt (contains_eq_true_iff map key).mp h), if_neg h]
end VerifiedHAMT.Map
