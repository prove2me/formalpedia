-- Prove2me | solution 1 for VerifiedHAMT.hasKey_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:25:43.913675+00:00
-- url     : https://prove2.me/submissions/5d947acc-340d-48b5-b757-c76f207f0e3a

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {es : Array (Entry α β (Node α β))} {key : α} :
    HasKey key (.entries es) ↔ ∃ (i : Nat) (hi : i < es.size), EntryHasKey key es[i] := by
  constructor
  · intro h
    cases h with
    | @entry _ i hi v h => exact ⟨i, hi, by simp [h, EntryHasKey]⟩
    | @ref _ i hi child h hk => exact ⟨i, hi, by simpa [h, EntryHasKey] using hk⟩
  · rintro ⟨i, hi, hk⟩
    cases h : es[i] with
    | null => simp [h, EntryHasKey] at hk
    | entry key' v =>
      have heq : key = key' := by simpa [h, EntryHasKey] using hk
      subst key'
      exact HasKey.entry h
    | ref child =>
      exact HasKey.ref h (by simpa [h, EntryHasKey] using hk)
end VerifiedHAMT
