-- Prove2me | solution 1 for P2M_VerifiedHAMT_find__eq_none_iff_fb022f809bac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:51.21479+00:00
-- url     : https://prove2.me/submissions/ce0cecd4-86c1-431f-b0a6-5404a444bedd

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_VerifiedHAMT_findNode_eq_none_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    VerifiedHAMT.find? map key = none ↔ ¬ Mem key map := findNode_eq_none_iff wf key
end VerifiedHAMT
