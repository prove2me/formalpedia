-- Prove2me | solution 1 for VerifiedHAMT.insertEntries_wf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:27.102496+00:00
-- url     : https://prove2.me/submissions/9121f66b-bb9c-4f19-9e2f-4b419915df72

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
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_hasKey_set_iff
public import Theorems.Thm_VerifiedHAMT_insertEntries_eq
public import Theorems.Thm_VerifiedHAMT_wellFormed_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_wellFormed_set


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
    (wf : WellFormed hashAt (.entries es))
    (childSpec : ∀ (child : Node α β) (hmem : .ref child ∈ es),
      letI res := (childInsert child hmem (nextHash (hashAt key)) key value)
      WellFormed (fun q => nextHash (hashAt q)) res ∧
        ∀ q, HasKey q res ↔
          q = key ∨ HasKey q child) :
    letI res := insertEntries es childInsert (hashAt key) key value
    WellFormed hashAt (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        q = key ∨ HasKey q (.entries es) := by
  have hi := wf.slot_lt (hashAt key)
  have finish (e : Entry α β (Node α β))
      (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[slot (hashAt key)])
      (hc : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
      letI res := (.entries (es.set (slot (hashAt key)) e))
      WellFormed hashAt res ∧
        ∀ q, HasKey q res ↔
          q = key ∨ HasKey q (.entries es) := by
    constructor
    · apply wellFormed_set wf _ hi e _ hc
      cases wf <;> grind
    · exact hasKey_set_iff _ hi e key mem
  rw [insertEntries_eq _ _ _ _ _ hi]
  split
  · apply finish <;> grind [EntryHasKey]
  · split <;> apply finish <;>
      grind [EntryHasKey, hasKey_mkCollisionNode, wellFormed_mkCollisionNode]
  · rename_i child hmem he _
    have := childSpec child hmem
    apply finish <;> grind [EntryHasKey]
end VerifiedHAMT
