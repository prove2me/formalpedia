-- Prove2me | solution 1 for ThreeSum.SparseBoxes.boxSum_resolve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:50.080078+00:00
-- url     : https://prove2.me/submissions/09a4c1f7-3e2e-4b0e-8cdf-d0dfc983945d

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
theorem _root_.solution (flags free : Finset α) (weight : Finset α → ℤ)
    (a : α) (hfree : free ⊆ flags) (ha : a ∈ free) :
    boxSum flags free weight =
      boxSum flags (free.erase a) weight +
      boxSum (flags.erase a) (free.erase a) weight := by
  have haf : a ∈ flags := hfree ha
  have hdinc : flags \ free.erase a = insert a (flags \ free) := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [haf]
    · simp [hxa]
  have hdexc : flags.erase a \ free.erase a = flags \ free := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ha]
    · simp [hxa]
  have hinc : boxSum flags (free.erase a) weight =
      ∑ leaf ∈ flags.powerset,
        if flags \ free ⊆ leaf ∧ a ∈ leaf then weight leaf else 0 := by
    unfold boxSum
    rw [hdinc]
    apply Finset.sum_congr rfl
    intro leaf hl
    simp only [Finset.insert_subset_iff, and_comm]
  have hexc : boxSum (flags.erase a) (free.erase a) weight =
      ∑ leaf ∈ flags.powerset,
        if flags \ free ⊆ leaf ∧ a ∉ leaf then weight leaf else 0 := by
    unfold boxSum
    rw [hdexc]
    calc
      _ = ∑ leaf ∈ (flags.erase a).powerset,
            if flags \ free ⊆ leaf ∧ a ∉ leaf then weight leaf else 0 := by
        apply Finset.sum_congr rfl
        intro leaf hl
        have han : a ∉ leaf := by
          intro hal
          exact Finset.notMem_erase a flags ((Finset.mem_powerset.mp hl) hal)
        simp only [han, not_false_eq_true, and_true]
      _ = _ := by
        apply Finset.sum_subset
        · intro leaf hl
          exact Finset.mem_powerset.mpr
            ((Finset.mem_powerset.mp hl).trans (Finset.erase_subset a flags))
        · intro leaf hl hnl
          have hal : a ∈ leaf := by
            by_contra han
            apply hnl
            apply Finset.mem_powerset.mpr
            intro x hx
            refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_powerset.mp hl) hx⟩
            intro he
            subst x
            exact han hx
          simp only [hal, not_true_eq_false, and_false, ite_false]
  rw [hinc, hexc, ← Finset.sum_add_distrib]
  unfold boxSum
  apply Finset.sum_congr rfl
  intro leaf hl
  by_cases hr : flags \ free ⊆ leaf <;> by_cases hal : a ∈ leaf <;> simp [hr, hal]
end ThreeSum.SparseBoxes
