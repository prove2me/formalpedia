-- Prove2me | solution 1 for VerifiedHAMT.containsNode_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:31.714369+00:00
-- url     : https://prove2.me/submissions/d0debd01-4fe8-4171-9d80-5f63950af444

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
public import Theorems.Thm_VerifiedHAMT_containsNode_sound
public import Theorems.Thm_VerifiedHAMT_containsNode_complete

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) :
    containsNode node (hashAt key) key = true ↔ HasKey key node :=
  ⟨containsNode_sound node (hashAt key) key, containsNode_complete wf key⟩
end VerifiedHAMT
