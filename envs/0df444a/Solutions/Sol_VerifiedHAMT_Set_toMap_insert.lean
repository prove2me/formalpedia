-- Prove2me | solution 1 for VerifiedHAMT.Set.toMap_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:29.140898+00:00
-- url     : https://prove2.me/submissions/ebeb5e64-1333-43b8-b8e9-059afeb77cdc

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).toMap = set.toMap.insert key () := rfl
end VerifiedHAMT.Set
