-- Prove2me | solution 1 for SatiaLave.MaxMin.inv_one_sub_smul_nonneg_diag_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:33.459236+00:00
-- url     : https://prove2.me/submissions/ce0fbe31-3ab2-4814-a75d-bd9bf55e8d10

import Mathlib

open Matrix

private theorem expand {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ) (β : ℝ)
    (x : S → ℝ) (i : S) :
    ∑ k, ((1 - β • P) i k) * x k = x i - β * ∑ k, P i k * x k := by
  have h1 : ∀ k : S, ((1 - β • P) i k) * x k
      = (if i = k then x k else 0) - β * (P i k * x k) := by
    intro k
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs with hik <;> ring
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq]
  simp

theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_sum : ∀ i, ∑ j, P i j = 1)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsUnit (1 - β • P) ∧ (∀ i j, 0 ≤ (1 - β • P)⁻¹ i j) ∧ ∀ i, 1 ≤ (1 - β • P)⁻¹ i i := by
  rcases isEmpty_or_nonempty S with hS | hS
  · have h1 : (1 - β • P) = 1 := by ext i j; exact (IsEmpty.false i).elim
    refine ⟨?_, fun i => (IsEmpty.false i).elim, fun i => (IsEmpty.false i).elim⟩
    rw [h1]
    exact isUnit_one
  have hdet : (1 - β • P).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    obtain ⟨i, hi⟩ := Finite.exists_max (fun k : S => |v k|)
    have hrow0 : ∑ k, ((1 - β • P) i k) * v k = 0 := by
      have hz : ((1 - β • P) *ᵥ v) i = 0 := by rw [hv]; simp
      rw [Matrix.mulVec_apply_eq_sum] at hz
      exact hz
    rw [expand P β v i] at hrow0
    have hveq : v i = β * ∑ k, P i k * v k := by linarith
    have hbd : |∑ k, P i k * v k| ≤ |v i| := by
      calc |∑ k, P i k * v k| ≤ ∑ k, |P i k * v k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, P i k * |v k| := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [abs_mul, abs_of_nonneg (hP_nonneg i k)]
        _ ≤ ∑ k, P i k * |v i| :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hi k) (hP_nonneg i k)
        _ = |v i| := by rw [← Finset.sum_mul, hP_sum i, one_mul]
    have habs : |v i| = β * |∑ k, P i k * v k| := by
      rw [hveq, abs_mul, abs_of_nonneg hβ0]
    have hle : |v i| ≤ β * |v i| :=
      calc |v i| = β * |∑ k, P i k * v k| := habs
        _ ≤ β * |v i| := mul_le_mul_of_nonneg_left hbd hβ0
    have hvi0 : |v i| = 0 := by
      by_contra hc
      have hpos : 0 < |v i| := (abs_nonneg _).lt_of_ne (Ne.symm hc)
      nlinarith [hle, hpos, mul_pos (sub_pos.mpr hβ1) hpos]
    apply hv0
    funext k
    have h2 : |v k| ≤ 0 := by rw [← hvi0]; exact hi k
    show v k = 0
    exact abs_nonpos_iff.mp h2
  have hunit : IsUnit (1 - β • P) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hmulinv : (1 - β • P) * (1 - β • P)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hrow : ∀ i j : S, ((1 - β • P)⁻¹ i j) - β * ∑ k, P i k * ((1 - β • P)⁻¹ k j)
      = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h1 : ∑ k, (1 - β • P) i k * ((1 - β • P)⁻¹ k j) = (1 : Matrix S S ℝ) i j := by
      rw [← Matrix.mul_apply, hmulinv]
    rw [← expand P β (fun k => (1 - β • P)⁻¹ k j) i, h1, Matrix.one_apply]
  have hnn : ∀ i j : S, 0 ≤ (1 - β • P)⁻¹ i j := by
    intro i j
    obtain ⟨i0, hi0⟩ := Finite.exists_min (fun k : S => (1 - β • P)⁻¹ k j)
    have hmin0 : 0 ≤ (1 - β • P)⁻¹ i0 j := by
      have he := hrow i0 j
      have hsum : (1 - β • P)⁻¹ i0 j ≤ ∑ k, P i0 k * ((1 - β • P)⁻¹ k j) := by
        calc (1 - β • P)⁻¹ i0 j = ∑ k, P i0 k * ((1 - β • P)⁻¹ i0 j) := by
              rw [← Finset.sum_mul, hP_sum i0, one_mul]
          _ ≤ ∑ k, P i0 k * ((1 - β • P)⁻¹ k j) :=
              Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hi0 k) (hP_nonneg i0 k)
      have hβsum : β * ((1 - β • P)⁻¹ i0 j) ≤ β * ∑ k, P i0 k * ((1 - β • P)⁻¹ k j) :=
        mul_le_mul_of_nonneg_left hsum hβ0
      have hδ : (0 : ℝ) ≤ if i0 = j then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      nlinarith [he, hβsum, hδ, sub_pos.mpr hβ1]
    exact le_trans hmin0 (hi0 i)
  refine ⟨hunit, hnn, ?_⟩
  intro i
  have he : (1 - β • P)⁻¹ i i - β * ∑ k, P i k * ((1 - β • P)⁻¹ k i) = 1 := by
    have h := hrow i i
    simpa using h
  have hs : 0 ≤ ∑ k, P i k * ((1 - β • P)⁻¹ k i) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hP_nonneg i k) (hnn k i)
  nlinarith [he, mul_nonneg hβ0 hs]
