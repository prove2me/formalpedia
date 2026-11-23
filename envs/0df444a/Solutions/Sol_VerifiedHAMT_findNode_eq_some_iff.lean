-- Prove2me | solution 1 for VerifiedHAMT.findNode_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:35.938008+00:00
-- url     : https://prove2.me/submissions/4cd2a38a-b9f4-4843-b660-c4acfbd274b3

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_VerifiedHAMT_findNode_sound
public import Theorems.Thm_VerifiedHAMT_findNode_exists_of_hasKey
public import Theorems.Thm_VerifiedHAMT_EntryHasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_HasBinding_functional
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (hu : Unique node)
    (key : α) (value : β) :
    findNode node (hashAt key) key = some value ↔ HasBinding key value node := by
  constructor
  · exact findNode_sound node (hashAt key) key value
  · intro hb
    obtain ⟨actual, ha⟩ := findNode_exists_of_hasKey wf key hb.hasKey
    have he := HasBinding.functional wf hu (findNode_sound _ _ _ _ ha) hb
    simpa [he] using ha
end VerifiedHAMT
