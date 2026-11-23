-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertEntries_wf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:20.57288+00:00
-- url     : https://prove2.me/submissions/e4a0341e-a64e-489f-8e66-44bff89b1937

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_WellFormed_slot_lt
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_set_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_eq
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_set
public import Theorems.Thm_VerifiedHAMT_WellFormed_slot_lt
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_hasKey_set_iff
public import Theorems.Thm_VerifiedHAMT_wellFormed_mkCollisionNode


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α]
    (hashAt : α → USize) (es : Array (Entry α (Node α)))
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (key : α)
    (wf : WellFormed hashAt (.entries es))
    (childSpec : ∀ (child : Node α) (hmem : .ref child ∈ es),
      letI res := (childInsert child hmem (nextHash (hashAt key)) key)
      WellFormed (fun q => nextHash (hashAt q)) res ∧
        ∀ q, HasKey q res ↔
          q = key ∨ HasKey q child) :
    letI res := insertEntries es childInsert (hashAt key) key
    WellFormed hashAt (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        q = key ∨ HasKey q (.entries es) := by
  have hi := wf.slot_lt (hashAt key)
  have finish (e : Entry α (Node α))
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
  rw [insertEntries_eq _ _ _ _ hi]
  split
  · apply finish <;> grind [EntryHasKey]
  · split <;> apply finish <;>
      grind [EntryHasKey, hasKey_mkCollisionNode, wellFormed_mkCollisionNode]
  · rename_i child hmem he _
    have := childSpec child hmem
    apply finish <;> grind [EntryHasKey]
end VerifiedHAMT.SetWithoutValArray.Raw
