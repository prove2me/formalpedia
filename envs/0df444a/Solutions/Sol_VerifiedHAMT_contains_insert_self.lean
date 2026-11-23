-- Prove2me | solution 1 for VerifiedHAMT.contains_insert_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:02.445974+00:00
-- url     : https://prove2.me/submissions/4a2223eb-bf20-4726-9491-7cc458e81a88

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_self
public import Theorems.Thm_VerifiedHAMT_contains_insert
attribute [local simp] VerifiedHAMT.mapsTo_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) (value : β) :
    contains (insert map key value) key = true := by
  simp [contains_insert map wf]
end VerifiedHAMT
