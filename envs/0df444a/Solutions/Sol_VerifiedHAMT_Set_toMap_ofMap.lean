-- Prove2me | solution 1 for VerifiedHAMT.Set.toMap_ofMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:00.769906+00:00
-- url     : https://prove2.me/submissions/a7598546-e81c-4b9b-9318-48990b9f26d5

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
theorem _root_.solution (map : Map α Unit) : (ofMap map).toMap = map := rfl
end VerifiedHAMT.Set
