-- Prove2me | solution 1 for VerifiedHAMT.Set.contains_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:54.993605+00:00
-- url     : https://prove2.me/submissions/5dfddb84-cceb-4d81-a956-b582cdf3472d

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set
public import Theorems.Thm_VerifiedHAMT_Map_contains_empty
public import Theorems.Thm_VerifiedHAMT_contains_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution [LawfulBEq α] (key : α) :
    (∅ : Set α).contains key = false := Map.contains_empty key
end VerifiedHAMT.Set
