-- Prove2me | solution 1 for VerifiedHAMT.Set.mem_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:12:58.096439+00:00
-- url     : https://prove2.me/submissions/7f00fdf2-ffa8-4b9d-a863-6983ef224b3e

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_mem_keys


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution (set : Set α) (key : α) : key ∈ set.toList ↔ key ∈ set :=
  Map.mem_keys set.toMap key
end VerifiedHAMT.Set
