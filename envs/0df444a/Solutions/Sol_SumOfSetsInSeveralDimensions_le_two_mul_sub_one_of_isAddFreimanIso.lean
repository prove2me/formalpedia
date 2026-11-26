-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.le_two_mul_sub_one_of_isAddFreimanIso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:24.331196+00:00
-- url     : https://prove2.me/submissions/6150ce4c-89e2-4b7e-9d53-085b1a9dfa8b

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
public import Theorems.Thm_Finset_affineDim_add_one_le_card
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset


section
@[expose] public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
private lemma sum_Ico_one_min_eq_choose {r : ℕ} (hr : 1 ≤ r) :
    ∑ s ∈ Ico 1 r, min (r - 1) s = r.choose 2 := by
  rw [sum_congr rfl (g := id) (by grind), ← Nat.sub_add_cancel hr, Ico_add_one_right_eq_Icc]
  simpa using Nat.sum_Icc_choose (r - 1) 1
private lemma sum_Ico_min_eq_mul {b r : ℕ} :
    ∑ s ∈ Ico r b, min (r - 1) s = (b - r) * (r - 1) := by
  rw [sum_congr rfl (g := fun _ ↦ r - 1) (by grind)]
  simp
private lemma sum_Icc_min_sub {b r : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b) :
    ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) = r.choose 2 + (b - r) * (r - 1) := by
  rw [← sum_Ico_one_min_eq_choose hr, ← sum_Ico_min_eq_mul, sum_Ico_consecutive _ hr hrb,
    ← Ico_add_one_right_eq_Icc, Nat.sub_add_cancel (hr.trans hrb)]
  convert sum_Ico_reflect (fun s ↦ min (r - 1) s) 1 (Nat.le_succ b) using 3 <;> grind
private lemma add_one_le_two_mul_of_add_choose_add_le {b r : ℕ} {κ : ℝ} (hr : 1 ≤ r)
    (hrb : r ≤ b) (hbound : ((b + (r.choose 2 + (b - r) * (r - 1)) : ℕ) : ℝ) ≤ κ * b) :
    (r : ℝ) + 1 ≤ 2 * κ := by
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two, Nat.cast_sub hrb,
    Nat.cast_pred hr] at hbound
  nlinarith [mul_nonneg (sub_nonneg.2 (mod_cast hrb : (r : ℝ) ≤ b))
    (sub_nonneg.2 (mod_cast hr : (1 : ℝ) ≤ r)), (mod_cast hr.trans hrb : (1 : ℝ) ≤ b)]
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
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : (X.image f).affineDim = r) : (r : ℝ) ≤ 2 * κ - 1 := by
  obtain rfl | hr := r.eq_zero_or_pos
  · grind [one_le_of_card_add_le hX hXX]
  have hrX : r ≤ #X := by
    grind [affineDim_add_one_le_card (hX.image f), card_image_of_injOn hf.bijOn.injOn]
  have h := card_add_sum_min_le_card_add_of_isAddFreimanIso hX le_rfl (by rwa [union_self])
    (by rwa [union_self])
  rw [sum_Icc_min_sub hr hrX] at h
  linarith [add_one_le_two_mul_of_add_choose_add_le hr hrX ((Nat.cast_le.2 h).trans hXX)]
end SumOfSetsInSeveralDimensions
