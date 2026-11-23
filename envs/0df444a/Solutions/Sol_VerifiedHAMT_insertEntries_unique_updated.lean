-- Prove2me | solution 1 for VerifiedHAMT.insertEntries_unique_updated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:27.734786+00:00
-- url     : https://prove2.me/submissions/c4b244db-e798-4835-87b3-d9b182886427

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_WellFormed_slot_lt
public import Theorems.Thm_VerifiedHAMT_hasBinding_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_insertEntries_eq
public import Theorems.Thm_VerifiedHAMT_unique_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_unique_set
public import Theorems.Thm_VerifiedHAMT_updated_set


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α β (Node α β)))
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (key : α) (value : β)
    (wf : WellFormed hashAt (.entries es)) (hu : Unique (.entries es))
    (childSpec : ∀ (child : Node α β) (hmem : .ref child ∈ es),
      letI res := childInsert child hmem (nextHash (hashAt key)) key value
      Unique child → Unique res ∧ Updated child res key value) :
    letI res := insertEntries es childInsert (hashAt key) key value
    Unique (.entries res) ∧ Updated (.entries es) (.entries res) key value := by
  have hi := wf.slot_lt (hashAt key)
  have finish (e : Entry α β (Node α β))
      (hc : ∀ n, e = .ref n → Unique n)
      (upd : ∀ q w, EntryHasBinding q w e ↔
        (q = key ∧ w = value) ∨ (q ≠ key ∧ EntryHasBinding q w es[slot (hashAt key)])) :
      letI res := .entries (es.set (slot (hashAt key)) e)
      Unique res ∧ Updated (.entries es) res key value :=
    ⟨unique_set hu _ hi e hc, updated_set wf key value hi e upd⟩
  rw [insertEntries_eq _ _ _ _ _ hi]
  split
  · apply finish <;> grind [EntryHasBinding]
  · split <;> apply finish <;>
      grind [EntryHasBinding, hasBinding_mkCollisionNode, unique_mkCollisionNode]
  · rename_i child hmem he _
    have hchild : Unique child := by cases hu <;> grind
    have := childSpec child hmem hchild
    apply finish <;> grind [EntryHasBinding, Updated]
end VerifiedHAMT
