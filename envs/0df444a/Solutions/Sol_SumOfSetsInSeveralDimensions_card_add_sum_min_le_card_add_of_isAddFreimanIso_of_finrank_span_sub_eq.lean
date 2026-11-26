-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:26.719462+00:00
-- url     : https://prove2.me/submissions/e5b5a1d6-69bb-4f55-99d4-e71e423c91b0

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso
public import Theorems.Thm_Finset_affineDim_eq_finrank_span_sub


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*}
    [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ}
    (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ
      (↑((A ∪ B).image f) - ↑((A ∪ B).image f) : Set (Fin r → ℝ))) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) :=
  card_add_sum_min_le_card_add_of_isAddFreimanIso hB hBA hf
    ((affineDim_eq_finrank_span_sub _).trans hdim)
end SumOfSetsInSeveralDimensions
