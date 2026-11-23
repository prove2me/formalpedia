-- Prove2me | solution 1 for VerifiedHAMT.Set.toRaw_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:39.458162+00:00
-- url     : https://prove2.me/submissions/fae1c1be-9b75-4c85-8819-be6f6fec5b83

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
    (set.insert key).toRaw = ⟨VerifiedHAMT.insert set.toMap.toRaw key ()⟩ := rfl
end VerifiedHAMT.Set
