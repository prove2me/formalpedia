-- Prove2me | solution 1 for VerifiedHAMT.contains_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:55.352203+00:00
-- url     : https://prove2.me/submissions/3a5b0f0a-5435-45f8-9701-ef0fe95fe686

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
public import Theorems.Thm_VerifiedHAMT_containsNode_eq_true_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    contains map key = true ↔ Mem key map :=
  containsNode_eq_true_iff wf key
end VerifiedHAMT
