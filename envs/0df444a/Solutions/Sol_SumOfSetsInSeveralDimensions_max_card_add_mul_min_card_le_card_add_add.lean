-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.max_card_add_mul_min_card_le_card_add_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:57.908804+00:00
-- url     : https://prove2.me/submissions/634c187b-b2ed-4e02-b7f3-a57016ee8be8

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D d : ℕ} {A B : Finset (Fin D → ℝ)}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hA : A.Nonempty) (hB : B.Nonempty)
    (hd : d ≤ (A + B).affineDim) :
    max #A #B + d * min #A #B ≤ #(A + B) + d * (d + 1) / 2 := by
  rcases le_total #B #A with h | h
  · rw [max_eq_left h, min_eq_right h]
    exact card_add_mul_card_le_card_add_add hB h hd
  · rw [max_eq_right h, min_eq_left h, add_comm A B]
    exact card_add_mul_card_le_card_add_add hA h (add_comm A B ▸ hd)
end SumOfSetsInSeveralDimensions
