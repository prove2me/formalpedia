-- Prove2me | solution 1 for VerifiedHAMT.findD_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:58:50.305432+00:00
-- url     : https://prove2.me/submissions/603a8ed8-201d-4fb7-a2b8-d8471b5ec41a

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_P2M_VerifiedHAMT_find__empty_a79d102e4768
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_4955d8018b2a
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_self_b1de16f2743e
public import Theorems.Thm_VerifiedHAMT_findD_empty
public import Theorems.Thm_VerifiedHAMT_findD_insert
attribute [local simp] VerifiedHAMT.find?_empty
attribute [local simp] VerifiedHAMT.find?_insert
attribute [local simp] VerifiedHAMT.find?_insert_self
attribute [local simp] VerifiedHAMT.findD_empty
attribute [local simp] VerifiedHAMT.findD_insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value fallback : β) : findD (VerifiedHAMT.insert map key value) key fallback = value := by
  rw [findD_insert map wf hu]
  simp
end VerifiedHAMT
