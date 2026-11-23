-- Prove2me | solution 1 for VerifiedHAMT.Set.mem_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:55:53.493254+00:00
-- url     : https://prove2.me/submissions/0cbc6bf1-ab85-41db-bb5c-61eb46260a76

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_mem_insert_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (set : Set α) (key q : α) :
    q ∈ set.insert key ↔ q = key ∨ q ∈ set := Map.mem_insert_iff set.toMap key q ()
end VerifiedHAMT.Set
