-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.hasKey_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:33:57.417374+00:00
-- url     : https://prove2.me/submissions/a9025b10-36f7-4aaa-9a3e-c2e27385e9b7

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_collision

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {es : Array (Entry α (Node α))} {key : α} :
    HasKey key (.entries es) ↔ ∃ (i : Nat) (hi : i < es.size), EntryHasKey key es[i] := by
  constructor
  · intro h
    cases h with
    | @entry _ i hi h => exact ⟨i, hi, by simp [h, EntryHasKey]⟩
    | @ref _ i hi child h hk => exact ⟨i, hi, by simpa [h, EntryHasKey] using hk⟩
  · rintro ⟨i, hi, hk⟩
    cases h : es[i] with
    | null => simp [h, EntryHasKey] at hk
    | entry key' =>
      have heq : key = key' := by simpa [h, EntryHasKey] using hk
      subst key'
      exact HasKey.entry h
    | ref child =>
      exact HasKey.ref h (by simpa [h, EntryHasKey] using hk)
end VerifiedHAMT.SetWithoutValArray.Raw
