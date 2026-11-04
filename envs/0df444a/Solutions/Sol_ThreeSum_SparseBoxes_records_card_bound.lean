-- Prove2me | solution 1 for ThreeSum.SparseBoxes.records_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:17.733894+00:00
-- url     : https://prove2.me/submissions/8d11b9ff-fd46-4b7c-b05a-8e993ff3a840

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
import Theorems.Thm_ThreeSum_SparseBoxes_records_card_layers
namespace ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
private theorem choose_mono_below_half {n i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n / 2) : n.choose i ≤ n.choose j := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      simp [hi]
  | succ j ih =>
      by_cases he : i = j + 1
      · simp [he]
      · have hij' : i ≤ j := by omega
        have hj' : j ≤ n / 2 := by omega
        exact (ih hij' hj').trans (Nat.choose_le_succ_of_lt_half_left (by omega))
end ThreeSum.SparseBoxes
set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (ambient : Finset α) (cut : ℕ)
    (hcut : cut ≤ ambient.card / 2) :
    (records ambient cut).card ≤
      (ambient.card + 1) ^ 2 * ambient.card.choose cut := by
  rw [records_card_layers]
  calc
    _ ≤ ∑ _j ∈ Finset.range (ambient.card + 1),
          (ambient.card + 1) * ambient.card.choose cut := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hjc : j ≤ cut
      · simp only [hjc, ite_true]
        exact Nat.mul_le_mul
          (by have hh := Nat.div_le_self ambient.card 2; omega)
          (choose_mono_below_half hjc hcut)
      · simp only [hjc, ite_false]
        exact Nat.zero_le _
    _ = _ := by simp [pow_two, Nat.mul_assoc]
end ThreeSum.SparseBoxes
