-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.rebuild_wf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:35.861509+00:00
-- url     : https://prove2.me/submissions/4fcd7fcd-aad7-43ff-8166-4f6e99ebfc6d

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_wf_mem

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α → USize → α → Node α) (offset : USize)
    (childSpec :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k,
        letI res := childInsert n (hashAt k) k
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (keys : Array α)
    (i : Nat) (es : Array (Entry α (Node α)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys, .mk ..⟩ i es
    WellFormed (fun q => (hash q).toUSize >>> offset) (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        HasKey q (.entries es) ∨ ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q := by
  rw [rebuild.eq_def]
  dsimp only
  split
  · rename_i hi
    have step := insertEntries_wf_mem (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i]
      wf (by
        cases wf <;> grind [Array.mem_iff_getElem])
    obtain ⟨hw, hm⟩ := solution childInsert offset childSpec keys (i + 1) _ step.1
    refine ⟨hw, ?_⟩
    intro q
    rw [hm, step.2]
    grind
  · exact ⟨wf, by grind⟩
termination_by keys.size - i
end VerifiedHAMT.SetWithoutValArray.Raw
