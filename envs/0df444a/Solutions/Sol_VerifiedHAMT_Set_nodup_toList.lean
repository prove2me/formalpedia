-- Prove2me | solution 1 for VerifiedHAMT.Set.nodup_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:00.680505+00:00
-- url     : https://prove2.me/submissions/0fa821fd-84be-4dce-9048-59e082a8e226

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_nodup_keys


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution (set : Set α) : set.toList.Nodup := Map.nodup_keys set.toMap
end VerifiedHAMT.Set
