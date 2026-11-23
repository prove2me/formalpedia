-- Prove2me | solution 1 for VerifiedHAMT.Set.mem_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:57:00.711042+00:00
-- url     : https://prove2.me/submissions/eed97ba1-cf3a-4333-8ee7-1603c521de07

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Set_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_Map_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_mem_insert_iff

attribute [local simp] VerifiedHAMT.Set.mem_insert_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (set : Set α) (key : α) :
    key ∈ set.insert key := (mem_insert_iff set key key).mpr (Or.inl rfl)
end VerifiedHAMT.Set
