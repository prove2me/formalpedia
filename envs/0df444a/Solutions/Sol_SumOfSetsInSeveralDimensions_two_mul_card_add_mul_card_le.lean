-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.two_mul_card_add_mul_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:47.95431+00:00
-- url     : https://prove2.me/submissions/1e07dc73-4380-425f-8408-df7e5e6e8cc7

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_mul_le_two_mul_sum_min_add
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_le


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D d : ℕ} {A B : Finset (Fin D → ℝ)}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ (A + B).affineDim) : 2 * (#A + d * #B) ≤ 2 * #(A + B) + d * (d + 1) := by
  grind [card_add_sum_min_le_card_add_of_le hB hBA hd,
    two_mul_mul_le_two_mul_sum_min_add d hB.card_pos hBA]
end SumOfSetsInSeveralDimensions
