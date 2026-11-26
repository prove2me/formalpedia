-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_isAddFreimanIso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:47.334788+00:00
-- url     : https://prove2.me/submissions/dd097861-b2c0-4507-bc22-8cf7d76cff3d

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_image_of_isAddFreimanIso
public import Theorems.Thm_Finset_affineDim_union_le_sum_add_one
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_le


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*} [DecidableEq G]
    [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ} (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : ((A ∪ B).image f).affineDim = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by
  have hcard {S : Finset G} (hS : S ⊆ A ∪ B) : #(S.image f) = #S :=
    card_image_of_injOn (hf.bijOn.injOn.mono (coe_subset.2 hS))
  have hA : A.Nonempty := card_pos.1 (hB.card_pos.trans_le hBA)
  have h := card_add_sum_min_le_card_add_of_le (d := r - 1) (hB.image f)
    (by rwa [hcard subset_union_left, hcard subset_union_right])
    (by grind [image_union, affineDim_union_le_sum_add_one (hA.image f) (hB.image f)])
  rwa [hcard subset_union_left, hcard subset_union_right,
    card_add_image_of_isAddFreimanIso hf subset_union_left subset_union_right] at h
end SumOfSetsInSeveralDimensions
