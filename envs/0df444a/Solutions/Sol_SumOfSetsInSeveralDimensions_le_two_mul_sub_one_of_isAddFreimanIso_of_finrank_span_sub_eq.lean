-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:16.308996+00:00
-- url     : https://prove2.me/submissions/0cb7aa9d-eac6-4f7a-a3f7-bb5cd1e5cdac

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso
public import Theorems.Thm_Finset_affineDim_eq_finrank_span_sub


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(X.image f) - ↑(X.image f) : Set (Fin r → ℝ))) =
      r) :
    (r : ℝ) ≤ 2 * κ - 1 :=
  le_two_mul_sub_one_of_isAddFreimanIso hX hXX hf
    ((affineDim_eq_finrank_span_sub _).trans hdim)
end SumOfSetsInSeveralDimensions
