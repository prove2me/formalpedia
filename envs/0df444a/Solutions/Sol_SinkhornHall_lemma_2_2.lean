-- Prove2me | solution 1 for SinkhornHall.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:19:50.999659+00:00
-- url     : https://prove2.me/submissions/3a24d2bc-bcf6-4ee4-b6a6-e07577628537

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

open SinkhornHall in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (X : Finset ι) (Y : Finset κ) (hXY : IsStable A X Y) :
    2 * (∑ i ∈ X, r i) + 2 * (∑ j ∈ Y, c j) - (∑ i, r i) - (∑ j, c j) ≤
      (∑ i, |(∑ j, A i j * x i * y j) - r i|) + (∑ j, |(∑ i, A i j * x i * y j) - c j|) := by
  classical
  set sX : ι → ℝ := fun i => if i ∈ X then -1 else 1 with hsX
  set sY : κ → ℝ := fun j => if j ∈ Y then -1 else 1 with hsY
  have hB0 : ∀ i j, 0 ≤ A i j * x i * y j := fun i j =>
    mul_nonneg (mul_nonneg (hA i j) (hx i).le) (hy j).le
  have step1 : ∀ i, sX i * ((∑ j, A i j * x i * y j) - r i) ≤
      |(∑ j, A i j * x i * y j) - r i| := by
    intro i
    simp only [hsX]
    split_ifs
    · linarith [neg_abs_le ((∑ j, A i j * x i * y j) - r i)]
    · linarith [le_abs_self ((∑ j, A i j * x i * y j) - r i)]
  have step2 : ∀ j, sY j * ((∑ i, A i j * x i * y j) - c j) ≤
      |(∑ i, A i j * x i * y j) - c j| := by
    intro j
    simp only [hsY]
    split_ifs
    · linarith [neg_abs_le ((∑ i, A i j * x i * y j) - c j)]
    · linarith [le_abs_self ((∑ i, A i j * x i * y j) - c j)]
  have b1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => step1 i
  have b2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => step2 j
  have hpos : 0 ≤ ∑ i, sX i * (∑ j, A i j * x i * y j) +
      ∑ j, sY j * (∑ i, A i j * x i * y j) := by
    have e : ∑ i, sX i * (∑ j, A i j * x i * y j) + ∑ j, sY j * (∑ i, A i j * x i * y j) =
        ∑ i, ∑ j, (sX i + sY j) * (A i j * x i * y j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm (f := fun j i => sY j * (A i j * x i * y j)), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    by_cases hi : i ∈ X <;> by_cases hj : j ∈ Y
    · have h0 : A i j = 0 := le_antisymm (not_lt.mp (hXY i hi j hj)) (hA i j)
      rw [h0]; simp
    · simp only [hsX, hsY, if_pos hi, if_neg hj]; nlinarith [hB0 i j]
    · simp only [hsX, hsY, if_neg hi, if_pos hj]; nlinarith [hB0 i j]
    · simp only [hsX, hsY, if_neg hi, if_neg hj]; nlinarith [hB0 i j]
  have hr' : ∑ i, sX i * r i = ∑ i, r i - 2 * ∑ i ∈ X, r i := by
    have : ∀ i, sX i * r i = r i - 2 * (if i ∈ X then r i else 0) := by
      intro i; simp only [hsX]; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hc' : ∑ j, sY j * c j = ∑ j, c j - 2 * ∑ j ∈ Y, c j := by
    have : ∀ j, sY j * c j = c j - 2 * (if j ∈ Y then c j else 0) := by
      intro j; simp only [hsY]; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsplit1 : ∑ i, sX i * ((∑ j, A i j * x i * y j) - r i) =
      ∑ i, sX i * (∑ j, A i j * x i * y j) - ∑ i, sX i * r i := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hsplit2 : ∑ j, sY j * ((∑ i, A i j * x i * y j) - c j) =
      ∑ j, sY j * (∑ i, A i j * x i * y j) - ∑ j, sY j * c j := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  linarith
