-- Prove2me | solution 1 for P2M_VerifiedHAMT_find__insert_of_ne_f04aac250363
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:57:40.1078+00:00
-- url     : https://prove2.me/submissions/360d668f-70bc-4d1f-aeb1-3c26db939863

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
attribute [local simp] VerifiedHAMT.find?_empty
attribute [local simp] VerifiedHAMT.find?_insert
attribute [local simp] VerifiedHAMT.find?_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value : β) (hne : q ≠ key) :
    VerifiedHAMT.find? (VerifiedHAMT.insert map key value) q = VerifiedHAMT.find? map q := by
  rw [find?_insert map wf hu]
  simp [hne]
end VerifiedHAMT
