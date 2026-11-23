-- Prove2me | solution 1 for P2M_VerifiedHAMT_find__empty_a79d102e4768
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:48:20.414874+00:00
-- url     : https://prove2.me/submissions/9a0b66af-ae6f-4900-84aa-f0e2f084d365

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac
public import Theorems.Thm_VerifiedHAMT_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_valid_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α] (key : α) :
    VerifiedHAMT.find? (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key = none :=
  (find?_eq_none_iff _ valid_empty key).mpr (not_mem_empty key)
end VerifiedHAMT
