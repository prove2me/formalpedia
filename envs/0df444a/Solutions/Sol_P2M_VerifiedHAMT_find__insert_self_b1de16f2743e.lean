-- Prove2me | solution 1 for P2M_VerifiedHAMT_find__insert_self_b1de16f2743e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:51:52.235188+00:00
-- url     : https://prove2.me/submissions/89c2d03d-6c79-49fc-8899-a65adb467761

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_P2M_VerifiedHAMT_find__empty_a79d102e4768
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_4955d8018b2a
attribute [local simp] VerifiedHAMT.find?_empty
attribute [local simp] VerifiedHAMT.find?_insert

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : VerifiedHAMT.find? (VerifiedHAMT.insert map key value) key = some value := by
  rw [find?_insert map wf hu]
  simp
end VerifiedHAMT
