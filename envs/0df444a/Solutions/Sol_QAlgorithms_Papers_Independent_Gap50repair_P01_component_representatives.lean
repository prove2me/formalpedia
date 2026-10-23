-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.component_representatives
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:37:04.582722+00:00
-- url     : https://prove2.me/submissions/2dbfd509-c5a3-4291-8e25-3939af7bf7e8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)
open Polynomial

namespace X4CZC

attribute [local instance] Classical.propDecidable

lemma roots_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) :
    (Matrix.diagonal d).charpoly.roots = Multiset.map d Finset.univ.val := by
  rw [Matrix.charpoly_diagonal]
  have : ∏ i, (X - C (d i)) = ((Finset.univ.val.map d).map fun a => X - C a).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]; rfl
  rw [this, roots_multiset_prod_X_sub_C]

lemma cx_diag {n : ℕ} (d : Coord n → ℝ) :
    complexify (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [complexify]
  · simp [complexify, Matrix.diagonal_apply_ne _ h]

lemma sum_count {α : Type*} [DecidableEq α] (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    ∑ z ∈ s.toFinset.filter p, s.count z = Multiset.card (s.filter p) := by
  rw [← Multiset.toFinset_sum_count_eq (s.filter p), Multiset.toFinset_filter]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Multiset.count_filter, if_pos (Finset.mem_filter.1 hz).2]

lemma rot_diag {n : ℕ} (d : Coord n → ℝ) :
    spectralRotation (Matrix.diagonal d) =
      (-1 : ℂ) ^ ((Finset.univ.filter fun i => d i < 0).card / 2) := by
  unfold spectralRotation eigenvalues algebraicMultiplicity
  rw [cx_diag, roots_diag]
  set s := Multiset.map (fun i => (d i : ℂ)) Finset.univ.val
  have hprod : ∏ z ∈ s.toFinset.filter (fun z => ‖z‖ = 1 ∧ z ≠ 1 ∧ z ≠ -1),
      z ^ (kreinPositive (Matrix.diagonal d) z / 2) = 1 := by
    rw [Finset.prod_eq_one]
    intro z hz
    exfalso
    obtain ⟨hz, h1, h2, h3⟩ := Finset.mem_filter.1 hz
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hz)
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    rcases abs_eq (zero_le_one) |>.1 h1 with h | h <;> simp [h] at h2 h3
  rw [hprod, mul_one]
  congr 1
  have : ∀ z ∈ (s.toFinset.filter fun z => z.im = 0 ∧ z.re < 0),
      Polynomial.rootMultiplicity z (Matrix.diagonal fun i => (d i : ℂ)).charpoly = s.count z := by
    intro z _
    rw [← Polynomial.count_roots, roots_diag]
  rw [Finset.sum_congr rfl this, sum_count, Multiset.filter_map, Multiset.card_map]
  congr 1
  rw [← Finset.filter_val, Finset.card_val]
  congr 1
  ext i; simp

lemma wPlus_diag (n : ℕ) : wPlus n = Matrix.diagonal (fun _ => -1) := by
  unfold wPlus; ext i j; by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

def dM (n : ℕ) : Coord n → ℝ := fun i => match i with
  | Sum.inl j => if j.val = 0 then 2 else -1
  | Sum.inr j => if j.val = 0 then 1/2 else -1

lemma wMinus_diag (n : ℕ) : wMinus n = Matrix.diagonal (dM n) := rfl

lemma symp_diag {n : ℕ} (d : Coord n → ℝ) (hd : ∀ i, d (Sum.inl i) * d (Sum.inr i) = 1) :
    IsSymplectic (Matrix.diagonal d) := by
  unfold IsSymplectic canonicalJ
  rw [Matrix.diagonal_transpose]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply]
  · split_ifs with h
    · subst h; rw [mul_comm]; linarith [hd a]
    · rfl
  · split_ifs with h
    · subst h; linarith [hd a]
    · rfl

lemma card_sum (m : ℕ) : (∑ j : Fin (m+1), if (j : ℕ) = 0 then (0:ℕ) else 1) = m := by
  rw [Fin.sum_univ_succ]; simp

theorem main {n : ℕ} (hn : 1 ≤ n) :
    IsSymplectic (wPlus n) ∧ 0 < (wPlus n-1).det ∧ spectralRotation (wPlus n) = (-1 : ℂ)^n ∧
    IsSymplectic (wMinus n) ∧ (wMinus n-1).det < 0 ∧ spectralRotation (wMinus n) = (-1 : ℂ)^(n-1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wPlus_diag]; exact symp_diag _ (fun i => by norm_num)
  · rw [wPlus_diag, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.det_diagonal]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
    rw [← two_mul, pow_mul]; norm_num
  · rw [wPlus_diag, rot_diag]
    congr 1
    simp only [show (-1 : ℝ) < 0 by norm_num, Finset.filter_true, Finset.card_univ,
      Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [wMinus_diag]
    refine symp_diag _ (fun i => ?_)
    simp only [dM]; split_ifs <;> norm_num
  · rw [wMinus_diag, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.det_diagonal,
      Fintype.prod_sum_type]
    simp only [dM, Pi.sub_apply, Pi.one_apply, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ]
    simp only [if_pos, Nat.succ_ne_zero, if_false, reduceIte, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    have : (0:ℝ) < (-1 - 1) ^ m * (-1 - 1) ^ m := by
      rw [← mul_pow]; positivity
    have e : (2 - 1 : ℝ) * (-1 - 1) ^ m * ((1 / 2 - 1) * (-1 - 1) ^ m) =
        -(1/2) * ((-1 - 1) ^ m * (-1 - 1) ^ m) := by ring
    rw [e]; exact mul_neg_of_neg_of_pos (by norm_num) this
  · rw [wMinus_diag, rot_diag]
    congr 1
    rw [Finset.card_filter, Fintype.sum_sum_type]
    have h1 : ∀ j : Fin (m+1), (if dM (m+1) (Sum.inl j) < 0 then 1 else 0) =
        if (j : ℕ) = 0 then (0:ℕ) else 1 := by
      intro j; by_cases hj : (j:ℕ) = 0 <;> simp [dM, hj]
    have h2 : ∀ j : Fin (m+1), (if dM (m+1) (Sum.inr j) < 0 then 1 else 0) =
        if (j : ℕ) = 0 then (0:ℕ) else 1 := by
      intro j; by_cases hj : (j:ℕ) = 0 <;> simp [dM, hj]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun j _ => h2 j), card_sum]
    omega

end X4CZC

theorem solution {n : ℕ} (hn : 1 ≤ n) :
    IsSymplectic (wPlus n) ∧ 0 < (wPlus n-1).det ∧ spectralRotation (wPlus n) = (-1 : ℂ)^n ∧
    IsSymplectic (wMinus n) ∧ (wMinus n-1).det < 0 ∧ spectralRotation (wMinus n) = (-1 : ℂ)^(n-1) :=
  X4CZC.main hn
