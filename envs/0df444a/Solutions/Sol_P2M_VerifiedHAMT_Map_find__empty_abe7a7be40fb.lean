-- Prove2me | solution 1 for P2M_VerifiedHAMT_Map_find__empty_abe7a7be40fb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:05:01.021201+00:00
-- url     : https://prove2.me/submissions/e0e14025-c1b0-4a79-9b72-304fd6aad5c2

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__empty_a79d102e4768


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (key : α) :
    (∅ : Map α β).find? key = none := VerifiedHAMT.find?_empty key
end VerifiedHAMT.Map
