-- Prove2me | solution 1 for VerifiedHAMT.Set.contains_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:12:44.108567+00:00
-- url     : https://prove2.me/submissions/dd28a7f6-1731-4edd-b0c6-a7122157eb83

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_contains_eq_false_iff
public import Theorems.Thm_VerifiedHAMT_contains_eq_false_iff


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (set : Set α) (key : α) :
    set.contains key = false ↔ key ∉ set := Map.contains_eq_false_iff set.toMap key
end VerifiedHAMT.Set
