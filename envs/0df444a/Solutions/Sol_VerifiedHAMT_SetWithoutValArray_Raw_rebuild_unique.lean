-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.rebuild_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:49.457702+00:00
-- url     : https://prove2.me/submissions/99a86db8-9cf4-4485-b2b8-d9151270cae7

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_unique
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
    (childWF :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k,
        letI res := childInsert n (hashAt k) k
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (childUnique :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → Unique n → ∀ k, Unique (childInsert n (hashAt k) k))
    (keys : Array α) (i : Nat) (es : Array (Entry α (Node α)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es))
    (hu : Unique (.entries es)) :
    Unique (.entries (rebuild childInsert offset ⟨.collision keys, .mk ..⟩ i es)) := by
  rw [rebuild.eq_def]
  dsimp only
  split
  · rename_i hi
    have stepWF := insertEntries_wf_mem (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i] wf (by
        cases wf <;> grind [Array.mem_iff_getElem])
    have stepUnique := insertEntries_unique (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i] wf hu (by
        cases wf <;> grind [Array.mem_iff_getElem])
    exact solution childInsert offset childWF childUnique keys (i + 1) _ stepWF.1 stepUnique
  · exact hu
termination_by keys.size - i
end VerifiedHAMT.SetWithoutValArray.Raw
