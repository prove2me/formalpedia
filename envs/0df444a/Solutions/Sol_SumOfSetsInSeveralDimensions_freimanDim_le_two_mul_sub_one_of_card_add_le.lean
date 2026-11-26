-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:16.867326+00:00
-- url     : https://prove2.me/submissions/09f3b74b-c718-4848-876f-962f5e806199

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso
section
@[expose] public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
private lemma one_le_of_card_add_le {G : Type*} [DecidableEq G] [AddCancelCommMonoid G] {κ : ℝ}
    {X : Finset G} (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X) : 1 ≤ κ := by
  have h : (#X : ℝ) ≤ κ * #X := (Nat.cast_le.2 (card_le_card_add_left hX)).trans hXX
  nlinarith [(mod_cast hX.card_pos : (0 : ℝ) < #X)]
end
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {κ : ℝ} {X : Finset G} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) : (freimanDim X : ℝ) ≤ 2 * κ - 1 := by
  classical
  obtain hr | hr := (freimanDim X).eq_zero_or_pos
  · rw [hr, Nat.cast_zero]
    linarith [one_le_of_card_add_le hX hXX]
  obtain ⟨f, hf, haff⟩ := Nat.findGreatest_of_ne_zero (rfl : freimanDim X = _) hr.ne'
  exact le_two_mul_sub_one_of_isAddFreimanIso hX hXX (isAddFreimanIso_rationalVectorToReal_comp hf)
    (by rwa [← image_image])
end SumOfSetsInSeveralDimensions
