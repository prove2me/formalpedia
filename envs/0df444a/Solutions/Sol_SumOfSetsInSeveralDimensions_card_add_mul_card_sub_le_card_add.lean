-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_mul_card_sub_le_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:29.245529+00:00
-- url     : https://prove2.me/submissions/c35466af-9132-478d-b5c8-032cc4ede363

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_card_add_mul_card_le

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D d : ℕ} {A B : Finset (Fin D → ℝ)}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ (A + B).affineDim) :
    (#A : ℝ) + d * #B - d * (d + 1) / 2 ≤ #(A + B) := by
  have h : (2 * (#A + d * #B) : ℝ) ≤ 2 * #(A + B) + d * (d + 1) :=
    mod_cast two_mul_card_add_mul_card_le hB hBA hd
  linarith
end SumOfSetsInSeveralDimensions
