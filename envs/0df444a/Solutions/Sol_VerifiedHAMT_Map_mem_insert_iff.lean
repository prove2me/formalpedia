-- Prove2me | solution 1 for VerifiedHAMT.Map.mem_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:21.618897+00:00
-- url     : https://prove2.me/submissions/9061a497-52fd-4ea6-adf1-bc74d69104e7

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_mem_insert_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key q : α) (value : β) :
    q ∈ map.insert key value ↔ q = key ∨ q ∈ map :=
  VerifiedHAMT.mem_insert_iff map.toRaw map.valid key q value
end VerifiedHAMT.Map
