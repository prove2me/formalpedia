-- Prove2me | solution 1 for VerifiedHAMT.Set.empty_eq_emptyc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:15.947779+00:00
-- url     : https://prove2.me/submissions/f662a2bb-69b0-4943-9c57-b0ccc25cd42c

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
theorem _root_.solution : (empty : Set α) = ∅ := rfl
end VerifiedHAMT.Set
