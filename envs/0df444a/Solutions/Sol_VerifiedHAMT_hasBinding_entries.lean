-- Prove2me | solution 1 for VerifiedHAMT.hasBinding_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:52.697874+00:00
-- url     : https://prove2.me/submissions/231a7243-45ba-4721-98ff-124b48961283

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_slot_zero
public import Theorems.Thm_VerifiedHAMT_valid_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_hasBinding_collision
attribute [local simp] VerifiedHAMT.hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.slot_zero
attribute [local simp] VerifiedHAMT.valid_empty
attribute [local simp] VerifiedHAMT.not_mem_empty
attribute [local simp] VerifiedHAMT.hasBinding_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {es : Array (Entry α β (Node α β))} {key : α} {value : β} :
    HasBinding key value (.entries es) ↔
      ∃ (i : Nat) (hi : i < es.size), EntryHasBinding key value es[i] := by
  constructor
  · intro h
    cases h with
    | @entry _ i hi h => exact ⟨i, hi, by simp [h, EntryHasBinding]⟩
    | @ref _ i hi child h hb => exact ⟨i, hi, by simpa [h, EntryHasBinding] using hb⟩
  · rintro ⟨i, hi, hb⟩
    cases h : es[i] with
    | null => simp [h, EntryHasBinding] at hb
    | entry k v =>
      obtain ⟨rfl, rfl⟩ := (show key = k ∧ value = v by simpa [h, EntryHasBinding] using hb)
      exact .entry h
    | ref child => exact .ref h (by simpa [h, EntryHasBinding] using hb)
end VerifiedHAMT
