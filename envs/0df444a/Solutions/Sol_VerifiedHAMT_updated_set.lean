-- Prove2me | solution 1 for VerifiedHAMT.updated_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:20.136273+00:00
-- url     : https://prove2.me/submissions/d2f46ed4-0549-414a-af9a-219fb565f2fa

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Bindings
public import Theorems.Thm_VerifiedHAMT_EntryHasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_hasBinding_entries


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
    (wf : WellFormed hashAt (.entries es)) (key : α) (value : β)
    (hi : slot (hashAt key) < es.size) (e : Entry α β (Node α β))
    (upd : ∀ q w, EntryHasBinding q w e ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ EntryHasBinding q w es[slot (hashAt key)])) :
    Updated (.entries es) (.entries (es.set (slot (hashAt key)) e)) key value := by
  intro q w
  simp [hasBinding_entries, Array.getElem_set, hasBinding_entries]
  have route : ∀ (j : Nat) (hj : j < es.size), EntryHasBinding q w es[j] →
      slot (hashAt q) = j := by
    cases wf with | entries _ routing _ => exact fun j hj h => routing j hj q h.hasKey
  constructor <;> grind
end VerifiedHAMT
