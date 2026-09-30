-- Prove2me | solution 1 for StochFictPlay.Supermodular.lemmaA2_weighted_sum_pos
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:33:09.829226+00:00
-- url     : https://prove2.me/submissions/4f2298cb-79ab-48ac-b56e-6d271885f064

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
open scoped BigOperators

private theorem prefix_extend {n : ℕ} (c : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) :
    (∑ i ∈ Finset.range j, (if h : i < n then c ⟨i,h⟩ else 0)) =
      ∑ k : Fin n, if k.val < j then c k else 0 := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ i ∈ Finset.range j, if h : i < n then (if i < j then c ⟨i,h⟩ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hj)
      intro i hi hin
      simp only [Finset.mem_range] at hi hin
      simp [hin]

theorem solution (n : ℕ) (b c : Fin n → ℝ) (hb : StrictMono b)
    (hc_le : ∀ j : ℕ, j ≤ n → ∑ k : Fin n, (if k.val < j then c k else 0) ≤ 0)
    (hc_lt : ∃ j : ℕ, j ≤ n ∧ ∑ k : Fin n, (if k.val < j then c k else 0) < 0)
    (hc_eq : ∑ k : Fin n, c k = 0) :
    0 < ∑ k : Fin n, b k * c k := by
  classical
  let B : ℕ → ℝ := fun i => if h : i < n then b ⟨i,h⟩ else 0
  let C : ℕ → ℝ := fun i => if h : i < n then c ⟨i,h⟩ else 0
  have hC (j : ℕ) (hj : j ≤ n) : (∑ i ∈ Finset.range j, C i) = ∑ k : Fin n, if k.val < j then c k else 0 := prefix_extend c j hj
  have hCn : ∑ i ∈ Finset.range n, C i = 0 := by simpa only [hC n le_rfl,Fin.is_lt,if_true] using hc_eq
  have hS : (∑ k : Fin n, b k*c k) = ∑ i ∈ Finset.range n, B i * C i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [B,C,Finset.mem_range.mp hi]
  have hB (i : ℕ) (hi : i < n-1) : 0 < B (i+1)-B i := by
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [B,dif_pos hi0,dif_pos hi1]
    exact sub_pos.mpr (hb (show (⟨i,hi0⟩ : Fin n) < ⟨i+1,hi1⟩ from by simp))
  obtain ⟨j,hjn,hj⟩ := hc_lt
  have hj0 : 0 < j := by
    by_contra h
    have hz : j=0 := by omega
    simp [hz] at hj
  have hjn' : j < n := by
    by_contra h
    have : j=n := by omega
    simp only [this,Fin.is_lt,if_true,hc_eq] at hj
    linarith
  have hneg : (∑ i ∈ Finset.range (n-1), (B (i+1)-B i) * ∑ k ∈ Finset.range (i+1), C k) < 0 := by
    apply Finset.sum_neg'
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      exact mul_nonpos_of_nonneg_of_nonpos (hB i hi').le (by rw [hC]; exact hc_le _ (by omega); omega)
    · refine ⟨j-1,Finset.mem_range.mpr (by omega),?_⟩
      have hj1 : j-1+1=j := by omega
      have hpre : (∑ k ∈ Finset.range (j-1+1), C k) < 0 := by rw [hj1,hC j hjn]; exact hj
      exact mul_neg_of_pos_of_neg (hB (j-1) (by omega)) hpre
  rw [hS]
  have hid := Finset.sum_range_by_parts B C n
  simp only [smul_eq_mul,hCn,mul_zero,zero_sub] at hid
  rw [hid]
  exact neg_pos.mpr hneg
