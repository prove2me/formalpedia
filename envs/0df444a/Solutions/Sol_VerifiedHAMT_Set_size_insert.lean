-- Prove2me | solution 1 for VerifiedHAMT.Set.size_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:22.252739+00:00
-- url     : https://prove2.me/submissions/23f0c903-9879-43ea-b2e8-6df9f27844e4

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_size_insert


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).size = if key ∈ set then set.size else set.size + 1 :=
  Map.size_insert set.toMap key ()
end VerifiedHAMT.Set
