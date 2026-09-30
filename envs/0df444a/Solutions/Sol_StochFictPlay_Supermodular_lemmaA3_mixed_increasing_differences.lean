-- Prove2me | solution 1 for StochFictPlay.Supermodular.lemmaA3_mixed_increasing_differences
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:36:19.551973+00:00
-- url     : https://prove2.me/submissions/74ce9f77-f2cc-4585-8e57-952277713084

import Definitions.Def_StochFictPlay_Supermodular_StochOrder
import Mathlib.Data.Matrix.Mul
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

private theorem weighted_pos (n : ℕ) (b c : Fin n → ℝ) (hb : StrictMono b)
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

open StochFictPlay.Supermodular
private theorem prefix_tail {m : ℕ} (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m))
    (i : Fin (m-1)) :
    (∑ j : Fin m, if j.val < i.val+1 then y j-x j else 0) = Tco x i-Tco y i := by
  have hid : (∑ j : Fin m, if j.val < i.val+1 then y j-x j else 0) + (Tco y i-Tco x i) =
      (∑ j : Fin m, y j) - ∑ j : Fin m, x j := by
    simp only [Tco,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i.val < j.val
    · have hji : ¬j.val < i.val+1 := by omega
      simp [hij,hji]
    · have hji : j.val < i.val+1 := by omega
      simp [hij,hji]
  rw [hx.2,hy.2] at hid
  linarith

private theorem order_iff (m : ℕ) (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m)) :
    Tco x ≤ Tco y ↔
      ∀ k : ℕ, k < m → ∑ i : Fin m, (if i.val < k then y i - x i else 0) ≤ 0 := by
  constructor
  · intro h k hk
    by_cases hk0 : k=0
    · simp [hk0]
    · let i : Fin (m-1) := ⟨k-1,by omega⟩
      have hik : i.val+1=k := by dsimp [i]; omega
      have hh := prefix_tail x y hx hy i
      rw [hik] at hh
      rw [hh]
      exact sub_nonpos.mpr (h i)
  · intro h i
    have hi : i.val+1 < m := by have := i.isLt; omega
    have hh := h (i.val+1) hi
    rw [prefix_tail x y hx hy i] at hh
    exact sub_nonpos.mp hh

private theorem prefix_step {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    (∑ k : Fin n, if k.val < j.val+1 then c k else 0) =
      (∑ k : Fin n, if k.val < j.val then c k else 0) + c j := by
  classical
  calc
    _ = ∑ k : Fin n, ((if k.val < j.val then c k else 0) + (if k=j then c k else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkj : k.val < j.val
      · have h1 : k.val < j.val+1 := by omega
        have hne : k ≠ j := by intro h; subst h; omega
        simp [hkj,h1,hne]
      · by_cases he : k=j
        · subst k; simp
        · have hv : k.val ≠ j.val := by intro h; exact he (Fin.ext h)
          have h1 : ¬k.val < j.val+1 := by omega
          simp [hkj,h1,he]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem solution {n₁ n₂ : ℕ} (A : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hA : ∀ i j : Fin n₁, i < j → StrictMono (fun k : Fin n₂ => A j k - A i k))
    (x y : Fin n₂ → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n₂)) (hy : y ∈ stdSimplex ℝ (Fin n₂))
    (hT : Tco x ≤ Tco y) (hne : y ≠ x) :
    StrictMono (fun i : Fin n₁ => Matrix.mulVec A y i - Matrix.mulVec A x i) := by
  have heq : ∑ k : Fin n₂, (y k-x k) = 0 := by rw [Finset.sum_sub_distrib,hx.2,hy.2,sub_self]
  have hle (j : ℕ) (hj : j ≤ n₂) : (∑ k : Fin n₂, if k.val < j then y k-x k else 0) ≤ 0 := by
    rcases lt_or_eq_of_le hj with hj|rfl
    · exact (order_iff n₂ x y hx hy).mp hT j hj
    · simpa only [Fin.is_lt,if_true,heq] using (le_refl (0:ℝ))
  have hlt : ∃ j : ℕ, j ≤ n₂ ∧ (∑ k : Fin n₂, if k.val < j then y k-x k else 0) < 0 := by
    by_contra h
    push_neg at h
    have hz (j : ℕ) (hj : j ≤ n₂) : (∑ k : Fin n₂, if k.val < j then y k-x k else 0) = 0 := le_antisymm (hle j hj) (h j hj)
    apply hne
    funext j
    have hh := prefix_step (fun k => y k-x k) j
    rw [hz _ (by omega),hz _ (by omega)] at hh
    linarith
  intro i j hij
  have hw := weighted_pos n₂ (fun k => A j k-A i k) (fun k => y k-x k) (hA i j hij) hle hlt heq
  have hid : (∑ k : Fin n₂, (A j k-A i k)*(y k-x k)) =
      (Matrix.mulVec A y j-Matrix.mulVec A x j) - (Matrix.mulVec A y i-Matrix.mulVec A x i) := by
    simp only [Matrix.mulVec,dotProduct,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hid] at hw
  exact sub_pos.mp hw
