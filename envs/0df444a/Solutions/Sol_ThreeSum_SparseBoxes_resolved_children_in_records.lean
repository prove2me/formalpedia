-- Prove2me | solution 1 for ThreeSum.SparseBoxes.resolved_children_in_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:51.330198+00:00
-- url     : https://prove2.me/submissions/d47830e4-45b1-45d0-b5f3-8ce1abdfb419

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Theorems.Thm_ThreeSum_SparseBoxes_IsInitial_erase_max_included
import Theorems.Thm_ThreeSum_SparseBoxes_IsInitial_erase_max_excluded
import Theorems.Thm_ThreeSum_SparseBoxes_mem_records

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (ambient flags free : Finset α) (cut : ℕ)
    (hfa : flags ⊆ ambient) (hcut : flags.card ≤ cut)
    (hinit : IsInitial flags free) (hn : free.Nonempty) :
    let a := free.max' hn
    (⟨flags, (free.erase a).card⟩ : Sigma (fun _ : Finset α => ℕ)) ∈ records ambient cut ∧
    (⟨flags.erase a, (free.erase a).card⟩ : Sigma (fun _ : Finset α => ℕ)) ∈
      records ambient cut ∧
    (free.erase a).card < free.card := by
  dsimp
  have hi := hinit.erase_max_included hn
  have he := hinit.erase_max_excluded hn
  refine ⟨(mem_records ambient flags cut _).mpr ⟨hfa, hcut, Finset.card_le_card hi.1⟩,
    (mem_records ambient (flags.erase _) cut _).mpr
      ⟨(Finset.erase_subset _ flags).trans hfa,
        (Finset.card_le_card (Finset.erase_subset _ flags)).trans hcut,
        Finset.card_le_card he.1⟩, ?_⟩
  rw [Finset.card_erase_of_mem (Finset.max'_mem free hn)]
  have hp := Finset.card_pos.mpr hn
  omega
end ThreeSum.SparseBoxes
