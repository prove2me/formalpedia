-- Prove2me | solution 1 for VerifiedHAMT.Set.length_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:14.274455+00:00
-- url     : https://prove2.me/submissions/258c646f-9fa7-4883-818d-b4e0b5bf1bba

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_length_keys


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution (set : Set α) : set.toList.length = set.size :=
  Map.length_keys set.toMap
end VerifiedHAMT.Set
