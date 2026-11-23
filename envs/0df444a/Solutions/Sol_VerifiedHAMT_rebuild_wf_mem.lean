-- Prove2me | solution 1 for VerifiedHAMT.rebuild_wf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:09.575147+00:00
-- url     : https://prove2.me/submissions/253a32ca-6de9-4504-8486-05d296f245b6

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_insertEntries_wf_mem

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α β → USize → α → β → Node α β) (offset : USize)
    (childSpec :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (es : Array (Entry α β (Node α β)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys vals hsz, .mk ..⟩ i es
    WellFormed (fun q => (hash q).toUSize >>> offset) (.entries res) ∧
      ∀ q, HasKey q (.entries res) ↔
        HasKey q (.entries es) ∨ ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q := by
  rw [rebuild.eq_def]
  dsimp only
  split
  · rename_i hi
    have step := insertEntries_wf_mem (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i]
      (vals[i]'(hsz ▸ hi)) wf (by
        cases wf <;> grind [Array.mem_iff_getElem])
    obtain ⟨hw, hm⟩ := solution childInsert offset childSpec keys vals hsz (i + 1) _ step.1
    refine ⟨hw, ?_⟩
    intro q
    rw [hm, step.2]
    grind
  · exact ⟨wf, by grind⟩
termination_by keys.size - i
end VerifiedHAMT
