-- Prove2me | solution 1 for SpectrumLB.proposition_5_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:01:40.989004+00:00
-- url     : https://prove2.me/submissions/ad7b6df6-81f0-4f39-bce3-2b7896931cf8

import Mathlib

open Finset Polynomial

def AB : ℕ → Finset ℕ × Finset ℕ
  | 0 => ({0}, ∅)
  | k + 1 => ((AB k).1 ∪ (AB k).2.map (addRightEmbedding (2 ^ k)),
              (AB k).2 ∪ (AB k).1.map (addRightEmbedding (2 ^ k)))

lemma AB_lt (k : ℕ) : (∀ n ∈ (AB k).1, n < 2 ^ k) ∧ (∀ n ∈ (AB k).2, n < 2 ^ k) := by
  induction k with
  | zero => simp [AB]
  | succ k ih =>
    simp only [AB, mem_union, mem_map, addRightEmbedding_apply]
    constructor
    · rintro n (h | ⟨m, hm, rfl⟩)
      · have := ih.1 n h; rw [pow_succ]; omega
      · have := ih.2 m hm; rw [pow_succ]; omega
    · rintro n (h | ⟨m, hm, rfl⟩)
      · have := ih.2 n h; rw [pow_succ]; omega
      · have := ih.1 m hm; rw [pow_succ]; omega

lemma disj1 (k : ℕ) : Disjoint (AB k).1 ((AB k).2.map (addRightEmbedding (2 ^ k))) := by
  rw [disjoint_left]
  intro n hn hn'
  simp only [mem_map, addRightEmbedding_apply] at hn'
  obtain ⟨m, _, rfl⟩ := hn'
  have := (AB_lt k).1 _ hn; omega

lemma disj2 (k : ℕ) : Disjoint (AB k).2 ((AB k).1.map (addRightEmbedding (2 ^ k))) := by
  rw [disjoint_left]
  intro n hn hn'
  simp only [mem_map, addRightEmbedding_apply] at hn'
  obtain ⟨m, _, rfl⟩ := hn'
  have := (AB_lt k).2 _ hn; omega

def D (k : ℕ) (f : ℕ → ℤ) : ℤ := ∑ n ∈ (AB k).1, f n - ∑ n ∈ (AB k).2, f n

lemma D_succ (k : ℕ) (f : ℕ → ℤ) : D (k + 1) f = D k (fun n => f n - f (n + 2 ^ k)) := by
  simp only [D, AB]
  rw [sum_union (disj1 k), sum_union (disj2 k), sum_map, sum_map]
  simp only [addRightEmbedding_apply, sum_sub_distrib]
  ring

lemma D_zero (f : ℕ → ℤ) : D 0 f = f 0 := by simp [D, AB]

lemma card_AB (k : ℕ) (hk : 1 ≤ k) : (AB k).1.card = 2 ^ (k - 1) ∧ (AB k).2.card = 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simp [AB]
  | succ k hk ih =>
    simp only [AB]
    rw [card_union_of_disjoint (disj1 k), card_union_of_disjoint (disj2 k), card_map, card_map,
      ih.1, ih.2]
    have : k + 1 - 1 = (k - 1) + 1 := by omega
    rw [this, pow_succ]; constructor <;> ring

lemma coeff_comp_shift_gen (q : ℤ[X]) (N : ℕ) (hq : q.natDegree < N) (h : ℤ) (m : ℕ) :
    (q.comp (X + C h)).coeff m = ∑ i ∈ range N, q.coeff i * (h ^ (i - m) * (i.choose m : ℤ)) := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_over_range' _ (fun n => by simp) N hq,
    Polynomial.finset_sum_coeff]
  apply sum_congr rfl; intro i _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]

lemma coeff_top (q : ℤ[X]) (k : ℕ) (hq : q.natDegree ≤ k + 1) (h : ℤ) :
    (q.comp (X + C h)).coeff (k + 1) = q.coeff (k + 1) := by
  rw [coeff_comp_shift_gen q (k + 2) (by omega) h (k + 1), sum_range_succ,
    sum_eq_zero (fun i hi => by
      have : i < k + 1 := mem_range.mp hi
      rw [Nat.choose_eq_zero_of_lt this]; simp)]
  simp

lemma coeff_next (q : ℤ[X]) (k : ℕ) (hq : q.natDegree ≤ k + 1) (h : ℤ) :
    (q.comp (X + C h)).coeff k = q.coeff k + (k + 1) * h * q.coeff (k + 1) := by
  rw [coeff_comp_shift_gen q (k + 2) (by omega) h k, sum_range_succ, sum_range_succ,
    sum_eq_zero (fun i hi => by
      have : i < k := mem_range.mp hi
      rw [Nat.choose_eq_zero_of_lt this]; simp)]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, zero_add,
    show k + 1 - k = 1 by omega, pow_one, Nat.choose_succ_self_right]
  push_cast; ring

lemma D_poly (k : ℕ) : ∀ q : ℤ[X], q.natDegree ≤ k →
    D k (fun n => q.eval (n : ℤ)) = (-1) ^ k * (k.factorial : ℤ) * (∏ i ∈ range k, (2:ℤ) ^ i) *
      q.coeff k := by
  induction k with
  | zero =>
    intro q hq
    rw [D_zero]
    rw [Polynomial.eq_C_of_natDegree_le_zero hq]
    simp
  | succ k ih =>
    intro q hq
    rw [D_succ]
    set r := q - q.comp (X + C ((2:ℤ) ^ k)) with hr
    have hev : (fun n : ℕ => q.eval (n : ℤ) - q.eval ((n + 2 ^ k : ℕ) : ℤ)) =
        fun n : ℕ => r.eval (n : ℤ) := by
      funext n; simp [hr, Polynomial.eval_comp]
    rw [hev]
    have hrdeg : r.natDegree ≤ k := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hcompdeg : (q.comp (X + C ((2:ℤ) ^ k))).natDegree ≤ k + 1 := by
        refine (Polynomial.natDegree_comp_le).trans ?_
        have : (X + C ((2:ℤ) ^ k)).natDegree = 1 := Polynomial.natDegree_X_add_C _
        rw [this, mul_one]; exact hq
      rcases Nat.lt_or_ge (k + 1) N with hlt | hge
      · rw [hr, Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
      · have hN' : N = k + 1 := by omega
        rw [hN', hr, Polynomial.coeff_sub, coeff_top q k hq, sub_self]
    rw [ih r hrdeg, hr, Polynomial.coeff_sub, coeff_next q k hq, prod_range_succ,
      Nat.factorial_succ]
    push_cast
    ring

lemma D_shift_pow (k j : ℕ) (hj : j ≤ k) :
    D k (fun n => ((n : ℤ) + 1) ^ j) = (-1) ^ k * (k.factorial : ℤ) * (∏ i ∈ range k, (2:ℤ) ^ i) *
      ((X + C (1:ℤ)) ^ j).coeff k := by
  have h := D_poly k ((X + C (1:ℤ)) ^ j) (by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]; exact hj)
  rw [← h]
  congr 1; funext n; simp

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    ∃ a b : Fin (2 ^ (k - 1)) → ℕ, (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
      (∀ j : ℕ, j < k → ∑ i, a i ^ j = ∑ i, b i ^ j) ∧ ∑ i, a i ^ k ≠ ∑ i, b i ^ k := by
  obtain ⟨hA, hB⟩ := card_AB k hk
  set A := (AB k).1
  set B := (AB k).2
  let a : Fin (2 ^ (k - 1)) → ℕ := fun i => (A.equivFin.symm (Fin.cast hA.symm i) : ℕ) + 1
  let b : Fin (2 ^ (k - 1)) → ℕ := fun i => (B.equivFin.symm (Fin.cast hB.symm i) : ℕ) + 1
  have hsumA : ∀ j, ∑ i, a i ^ j = ∑ n ∈ A, (n + 1) ^ j := by
    intro j
    rw [← Finset.sum_coe_sort A (fun n => (n + 1) ^ j)]
    exact Fintype.sum_equiv ((finCongr hA.symm).trans A.equivFin.symm) _ _ (fun i => rfl)
  have hsumB : ∀ j, ∑ i, b i ^ j = ∑ n ∈ B, (n + 1) ^ j := by
    intro j
    rw [← Finset.sum_coe_sort B (fun n => (n + 1) ^ j)]
    exact Fintype.sum_equiv ((finCongr hB.symm).trans B.equivFin.symm) _ _ (fun i => rfl)
  have hD : ∀ j, ((∑ n ∈ A, (n + 1) ^ j : ℕ) : ℤ) - ((∑ n ∈ B, (n + 1) ^ j : ℕ) : ℤ) =
      D k (fun n => ((n : ℤ) + 1) ^ j) := by
    intro j; simp [D, A, B]
  have hc : (-1:ℤ) ^ k * (k.factorial : ℤ) * (∏ i ∈ range k, (2:ℤ) ^ i) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast k.factorial_ne_zero))
    exact prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (by norm_num))
  refine ⟨a, b, fun i => Nat.succ_pos _, fun i => Nat.succ_pos _, fun j hj => ?_, ?_⟩
  · rw [hsumA, hsumB]
    have h := hD j
    rw [D_shift_pow k j hj.le, Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]; exact hj), mul_zero] at h
    exact_mod_cast sub_eq_zero.mp h
  · rw [hsumA, hsumB]
    intro heq
    have h := hD k
    rw [D_shift_pow k k le_rfl, Polynomial.coeff_X_add_C_pow] at h
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one] at h
    rw [heq, sub_self] at h
    exact hc h.symm
