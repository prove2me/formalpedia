-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sub_mul_sub_choose_le_sum_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:53.417509+00:00
-- url     : https://prove2.me/submissions/b7647c50-ff41-4d3a-8631-a94b69235f34

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
private lemma sub_one_mul_le_choose_add_choose (b r : ℕ) :
    (r - 1) * b ≤ b.choose 2 + (r + 1).choose 2 := by
  obtain _ | r := r
  · simp
  · rw [← Nat.cast_le (α := ℚ), Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    nlinarith [sq_nonneg ((r : ℚ) + 1 - b), (Nat.cast_nonneg r : (0 : ℚ) ≤ r),
      (Nat.cast_nonneg b : (0 : ℚ) ≤ b)]
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
theorem _root_.solution (b r : ℕ) :
    (r - 1) * b - (r + 1).choose 2 ≤ ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) := by
  rw [Nat.sub_le_iff_le_add]
  obtain hrb | hbr := le_total r b
  · obtain rfl | hr := r.eq_zero_or_pos
    · simp
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hrb
      rw [sum_Icc_min_sub hr hrb, Nat.add_sub_cancel_left, mul_add]
      linarith [sub_one_mul_le_choose_add_choose r r, mul_comm c (r - 1)]
  · obtain rfl | hb := b.eq_zero_or_pos
    · simp
    · refine (sub_one_mul_le_choose_add_choose b r).trans ?_
      rw [← add_zero (b.choose 2), ← zero_mul (b - 1), ← Nat.sub_self b,
        ← sum_Icc_min_sub hb le_rfl]
      gcongr
end SumOfSetsInSeveralDimensions
