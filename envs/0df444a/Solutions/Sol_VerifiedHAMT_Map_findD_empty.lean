-- Prove2me | solution 1 for VerifiedHAMT.Map.findD_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:05:06.043537+00:00
-- url     : https://prove2.me/submissions/02094fe8-6181-4b8a-afb6-95af6336188f

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_findD_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (key : α) (fallback : β) :
    (∅ : Map α β).findD key fallback = fallback := VerifiedHAMT.findD_empty key fallback
end VerifiedHAMT.Map
