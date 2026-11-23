-- Prove2me | solution 1 for P2M_VerifiedHAMT_find__eq_some_iff_ca0e0de371ba
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:57.427726+00:00
-- url     : https://prove2.me/submissions/0464475f-0fc8-4c75-8555-f4979df6f8d8

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_VerifiedHAMT_findNode_eq_some_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) : VerifiedHAMT.find? map key = some value ↔ MapsTo key value map :=
  findNode_eq_some_iff wf hu key value
end VerifiedHAMT
