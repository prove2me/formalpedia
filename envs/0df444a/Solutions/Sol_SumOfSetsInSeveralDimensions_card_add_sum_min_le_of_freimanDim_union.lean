-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_sum_min_le_of_freimanDim_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:28.285732+00:00
-- url     : https://prove2.me/submissions/ecd1afa1-b86d-464a-aba0-6cc257c85f05

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Theorems.Thm_SumOfSetsInSeveralDimensions_isAddFreimanIso_rationalVectorToReal_comp
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {A B : Finset G} (hr : 1 ≤ r) (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : freimanDim (A ∪ B) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by
  classical
  obtain ⟨f, hf, haff⟩ := Nat.findGreatest_of_ne_zero hdim (Nat.ne_of_gt hr)
  exact card_add_sum_min_le_card_add_of_isAddFreimanIso hB hBA
    (isAddFreimanIso_rationalVectorToReal_comp hf) (by rwa [← image_image])
end SumOfSetsInSeveralDimensions
