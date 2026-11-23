-- Prove2me | solution 1 for VerifiedHAMT.contains_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:59.471567+00:00
-- url     : https://prove2.me/submissions/e3019cc3-e017-4a52-8ca2-916c632cbd19

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
public import Theorems.Thm_VerifiedHAMT_contains_eq_false_iff
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
    contains (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) key = false :=
  (contains_eq_false_iff _ valid_empty key).mpr (not_mem_empty key)
end VerifiedHAMT
