-- Prove2me | solution 1 for ShapleySnowSG.Kernel.lemma_2_2_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:52:37.059673+00:00
-- url     : https://prove2.me/submissions/0c92371d-3f28-4b18-8de6-b06ec2613685

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_StochasticGame

open Matrix

namespace SSKAux
open ShapleySnowSG.Kernel

lemma sum_ite_ne_add {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∑ j, (if j = i then 0 else f j) + f i = ∑ j, f j := by
  have : ∑ j, f j = ∑ j, ((if j = i then 0 else f j) + (if j = i then f j else 0)) :=
    Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i f]
  simp

/-- Ostrowski's lower bound for strictly row diagonally dominant matrices. -/
lemma ostrowski (n : ℕ) : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ), (∀ i, 0 < r i) →
    (∀ i, r i + ∑ j, (if j = i then 0 else |A i j|) ≤ A i i) → ∏ i, r i ≤ A.det := by
  induction n with
  | zero => intro A r _ _; simp
  | succ n ih =>
    intro A r hr hdom
    set a := A 0 0 with ha_def
    have hS0 : ∑ j : Fin n, |A 0 j.succ| ≤ a - r 0 := by
      have h := hdom 0
      rw [Fin.sum_univ_succ] at h
      simp only [if_true, Fin.succ_ne_zero, if_false, zero_add] at h
      linarith
    have hS0' : 0 ≤ ∑ j : Fin n, |A 0 j.succ| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have ha : r 0 ≤ a := by linarith
    have ha0 : 0 < a := lt_of_lt_of_le (hr 0) ha
    let A' : Matrix (Fin n) (Fin n) ℝ := fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / a
    have hdet : A.det = a * A'.det := by
      let c : Fin (n + 1) → ℝ := fun i => if i = 0 then 0 else A i 0 / a
      let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => A i j - c i * A 0 j
      have h1 : A.det = B.det := by
        refine det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c]) fun i j => ?_
        simp [B, c]
      rw [h1, det_succ_column_zero, Fin.sum_univ_succ]
      have h2 : ∀ k : Fin n, B k.succ 0 = 0 := by
        intro k
        simp only [B, c, Fin.succ_ne_zero, if_false]
        field_simp
        ring
      simp only [h2, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
        one_mul, Fin.succAbove_zero]
      congr 1
      · simp [B, c, a]
      · congr 1
        ext i j
        simp only [Matrix.submatrix, Matrix.of_apply, B, c, A', Fin.succ_ne_zero, if_false]
        ring
    have hdom' : ∀ i, r i.succ + ∑ j, (if j = i then 0 else |A' i j|) ≤ A' i i := by
      intro i
      set cc := A i.succ 0
      have h := hdom i.succ
      rw [Fin.sum_univ_succ] at h
      simp only [(Fin.succ_ne_zero i).symm, if_false, Fin.succ_inj] at h
      have e1 : ∑ j : Fin n, (if j = i then 0 else |A' i j|) ≤
          ∑ j : Fin n, (if j = i then 0 else |A i.succ j.succ|) +
          ∑ j : Fin n, (if j = i then 0 else |cc| * |A 0 j.succ| / a) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs
        · simp
        · simp only [A']
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_div, abs_mul, abs_of_pos ha0]
      have e2 := sum_ite_ne_add (fun j : Fin n => |cc| * |A 0 j.succ| / a) i
      have e3 : ∑ j : Fin n, |cc| * |A 0 j.succ| / a ≤ |cc| := by
        rw [← Finset.sum_div, ← Finset.mul_sum, div_le_iff₀ ha0]
        exact mul_le_mul_of_nonneg_left (by linarith [hr 0]) (abs_nonneg _)
      have e4 : -(|cc| * |A 0 i.succ| / a) ≤ -(cc * A 0 i.succ / a) := by
        rw [neg_le_neg_iff, ← abs_mul, ← abs_of_pos ha0, ← abs_div, abs_of_pos ha0]
        exact le_abs_self _
      have e5 : 0 ≤ |cc| * |A 0 i.succ| / a := by positivity
      simp only [A']
      simp only [A'] at e1
      linarith
    have hih := ih A' (fun i => r i.succ) (fun i => hr _) hdom'
    rw [Fin.prod_univ_succ, hdet]
    have hP : 0 ≤ ∏ i : Fin n, r i.succ := Finset.prod_nonneg fun i _ => (hr _).le
    exact mul_le_mul ha hih hP ha0.le

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {n : ℕ} (hn : 0 < n) {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    [∀ k, Nonempty (I k)] [∀ k, Nonempty (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ)
    (hq0 : ∀ k i j l, 0 ≤ q k i j l) (hq1 : ∀ k i j, ∑ l, q k i j l = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    ∀ i j, lam ^ n ≤ (-1) ^ n * Delta g q lam 0 i j := by
  intro a b
  let Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k m => q k (a k) (b k) m
  have h : Delta g q lam 0 a b = (-(1 - (1 - lam) • Q)).det := by
    simp only [Delta, aux, kronDet, dataArray, Fin.val_zero, pow_zero, one_smul]
    congr 1
    ext k m
    simp only [Matrix.of_apply, Fin.succAbove_zero, Fin.cases_succ, Q,
      Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, one_apply]
    by_cases hkm : k = m
    · subst hkm; simp
    · simp [hkm, Ne.symm hkm]
  rw [h, det_neg, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_mul]
  have hb := SSKAux.ostrowski n (1 - (1 - lam) • Q) (fun _ => lam) (fun _ => hlam0) (fun k => ?_)
  · simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hb
  · have hoff : ∀ j, (if j = k then 0 else |(1 - (1 - lam) • Q) k j|) =
        (1 - lam) * Q k j - (if j = k then (1 - lam) * Q k j else 0) := by
      intro j
      by_cases hjk : j = k
      · subst hjk; simp
      · have hQ : 0 ≤ Q k j := hq0 _ _ _ _
        rw [if_neg hjk, if_neg hjk, Matrix.sub_apply, one_apply_ne (Ne.symm hjk), Matrix.smul_apply,
          smul_eq_mul, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) hQ),
          sub_zero]
    rw [Finset.sum_congr rfl fun j _ => hoff j, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ k]
    simp only [Q, Matrix.of_apply, hq1, Finset.mem_univ, if_true, Matrix.sub_apply, one_apply_eq,
      Matrix.smul_apply, smul_eq_mul]
    linarith
