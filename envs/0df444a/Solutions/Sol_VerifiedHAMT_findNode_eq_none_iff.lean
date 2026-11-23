-- Prove2me | solution 1 for VerifiedHAMT.findNode_eq_none_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:39.859532+00:00
-- url     : https://prove2.me/submissions/86af20f1-0f7c-4078-9b40-9eb8fd3e5fb8

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
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) :
    findNode node (hashAt key) key = none ↔ ¬ HasKey key node := by
  constructor
  · intro hn hk
    obtain ⟨v, hv⟩ := findNode_exists_of_hasKey wf key hk
    rw [hn] at hv
    contradiction
  · intro hk
    cases he : findNode node (hashAt key) key with
    | none => rfl
    | some value => exact False.elim (hk (findNode_sound _ _ _ _ he).hasKey)
end VerifiedHAMT
