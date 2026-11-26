-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add_of_le_finrank_span_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:55.382375+00:00
-- url     : https://prove2.me/submissions/2d521bbb-e1e2-402c-a0cf-b1a270a35464

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
public import Theorems.Thm_Finset_affineDim_eq_finrank_span_sub


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D d : ℕ} {A B : Finset (Fin D → ℝ)}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hd : d ≤ Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ)))) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 :=
  card_add_mul_card_le_card_add_add hB hBA
    (hd.trans_eq (affineDim_eq_finrank_span_sub _).symm)
end SumOfSetsInSeveralDimensions
