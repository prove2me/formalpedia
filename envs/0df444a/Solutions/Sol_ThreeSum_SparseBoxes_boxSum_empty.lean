-- Prove2me | solution 1 for ThreeSum.SparseBoxes.boxSum_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:58.254272+00:00
-- url     : https://prove2.me/submissions/683fd4be-0adc-4d39-a80a-31b23f444d12

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

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (flags : Finset α) (weight : Finset α → ℤ) :
    boxSum flags ∅ weight = weight flags := by
  unfold boxSum
  simp only [Finset.sdiff_empty]
  rw [Finset.sum_eq_single flags]
  · simp
  · intro leaf hl hne
    have hn : ¬ flags ⊆ leaf := by
      intro hfl
      apply hne
      ext x
      exact ⟨fun hx => (Finset.mem_powerset.mp hl) hx, fun hx => hfl hx⟩
    simp only [hn, ite_false]
  · intro h
    exact False.elim (h (Finset.mem_powerset.mpr (Finset.Subset.refl flags)))
end ThreeSum.SparseBoxes
