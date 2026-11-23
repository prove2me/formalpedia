-- Prove2me | solution 1 for VerifiedHAMT.Set.toRaw_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:26.318578+00:00
-- url     : https://prove2.me/submissions/c0df3a4d-1a5c-4bd8-ae15-b9b49717c5aa

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
theorem _root_.solution :
    (∅ : Set α).toRaw = Lean.PersistentHashSet.empty := (rfl)
end VerifiedHAMT.Set
