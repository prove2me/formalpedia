-- Prove2me | solution 1 for VerifiedHAMT.hasKey_iff_exists_binding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:03.700806+00:00
-- url     : https://prove2.me/submissions/0e961954-bf92-46fb-acc7-82e4b2d72666

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_EntryHasBinding_hasKey

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {key : α} {node : Node α β} :
    HasKey key node ↔ ∃ value, HasBinding key value node := by
  constructor
  · intro h
    induction h with
    | @entry es i hi value he => exact ⟨value, .entry he⟩
    | ref he _ ih => obtain ⟨v, hv⟩ := ih; exact ⟨v, .ref he hv⟩
    | @collision keys vals hsz hk =>
      obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hk
      exact ⟨vals[i]'(hsz ▸ hi), .collision hi he rfl⟩
  · rintro ⟨v, h⟩; exact h.hasKey
end VerifiedHAMT
