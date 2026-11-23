-- Prove2me | solution 1 for VerifiedHAMT.Map.not_mem_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:11.108801+00:00
-- url     : https://prove2.me/submissions/e9502b9c-4da7-4aec-b6b6-93e438d0b87d

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_not_mem_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution (key : α) : key ∉ (∅ : Map α β) :=
  VerifiedHAMT.not_mem_empty key
end VerifiedHAMT.Map
