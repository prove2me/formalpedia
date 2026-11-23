-- Prove2me | solution 1 for VerifiedHAMT.Set.contains_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:56.552383+00:00
-- url     : https://prove2.me/submissions/b2566055-c087-4c4b-a2eb-c6ad07f6d7cb

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_contains_insert
public import Theorems.Thm_VerifiedHAMT_contains_insert


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (set : Set α) (key q : α) :
    (set.insert key).contains q = ((q == key) || set.contains q) :=
  Map.contains_insert set.toMap key q ()
end VerifiedHAMT.Set
