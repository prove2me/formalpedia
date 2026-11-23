-- Prove2me | solution 1 for VerifiedHAMT.Set.not_mem_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:50.226519+00:00
-- url     : https://prove2.me/submissions/16326178-1e8b-40db-89e4-96a3b8e82ea2

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution (key : α) : key ∉ (∅ : Set α) :=
  Map.not_mem_empty key
end VerifiedHAMT.Set
