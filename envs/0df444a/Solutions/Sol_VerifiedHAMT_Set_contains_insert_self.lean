-- Prove2me | solution 1 for VerifiedHAMT.Set.contains_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:58.136192+00:00
-- url     : https://prove2.me/submissions/8caee8f1-700c-4b4c-b7c4-47470edebe38

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_contains_insert_self
public import Theorems.Thm_VerifiedHAMT_contains_insert_self


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).contains key = true := Map.contains_insert_self set.toMap key ()
end VerifiedHAMT.Set
