-- Prove2me | solution 1 for VerifiedHAMT.Set.ofRaw_toRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:15.522801+00:00
-- url     : https://prove2.me/submissions/cafa1989-345a-492c-b552-dedf147f628b

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_ofRaw_toRaw


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution (set : Set α) :
    ofRaw set.toRaw set.toMap.valid set.toMap.unique = set :=
  congrArg Set.mk (Map.ofRaw_toRaw set.toMap)
end VerifiedHAMT.Set
