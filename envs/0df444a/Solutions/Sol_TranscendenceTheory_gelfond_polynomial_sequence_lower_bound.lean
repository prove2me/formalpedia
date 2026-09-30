-- Prove2me | solution 1 for TranscendenceTheory.gelfond_polynomial_sequence_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T02:35:08.133644+00:00
-- url     : https://prove2.me/submissions/1072a2b3-a945-42f2-9db0-27212ef8161f

import Mathlib.NumberTheory.MahlerMeasure
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

/-!
Complete proof of Gel'fond's polynomial-sequence criterion.

The proof follows the irreducible-factor/resultant stabilization argument of
Waldschmidt, Transcendence Methods (1979), §8.2, pp. 8.5–8.6, Theorem 8.2.1.
Factor selection uses additivity of degree and logarithmic Mahler measure.
All auxiliary results below are proved from Mathlib, without platform imports.
-/

open Polynomial
open scoped Polynomial

namespace TranscendenceTheory.Gelfond

noncomputable def logMeasure (p : ℤ[X]) : ℝ :=
  (p.map (Int.castRingHom ℂ)).logMahlerMeasure

noncomputable def logValue (θ : ℂ) (p : ℤ[X]) : ℝ :=
  Real.log ‖aeval θ p‖

noncomputable def weight (d t : ℝ) (p : ℤ[X]) : ℝ :=
  (p.natDegree : ℝ) * (t + 2 * d) + d * logMeasure p

lemma logMeasure_nonneg {p : ℤ[X]} (hp : p ≠ 0) : 0 ≤ logMeasure p := by
  simpa [logMeasure, logMahlerMeasure_eq_log_MahlerMeasure] using
    Real.log_nonneg (one_le_mahlerMeasure_of_ne_zero hp)

lemma logMeasure_mul {p q : ℤ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    logMeasure (p * q) = logMeasure p + logMeasure q := by
  unfold logMeasure
  rw [Polynomial.map_mul, logMahlerMeasure_mul_eq_add_logMahlerMeasure]
  exact mul_ne_zero
    ((Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hp)
    ((Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hq)

lemma logValue_mul {θ : ℂ} {p q : ℤ[X]}
    (hp : aeval θ p ≠ 0) (hq : aeval θ q ≠ 0) :
    logValue θ (p * q) = logValue θ p + logValue θ q := by
  simp only [logValue, map_mul, norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hq)

lemma weight_mul {d t : ℝ} {p q : ℤ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    weight d t (p * q) = weight d t p + weight d t q := by
  simp only [weight, natDegree_mul hp hq, Nat.cast_add, logMeasure_mul hp hq]
  ring

lemma weight_nonneg {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t)
    {p : ℤ[X]} (hp : p ≠ 0) : 0 ≤ weight d t p := by
  unfold weight
  have := logMeasure_nonneg hp
  positivity

lemma logMeasure_le_of_coeff_bound {p : ℤ[X]} (hp : p ≠ 0) {d t : ℝ}
    (hdeg : (p.natDegree : ℝ) ≤ d)
    (hcoeff : ∀ k, |(p.coeff k : ℝ)| ≤ Real.exp t) :
    logMeasure p ≤ t + Real.log (d + 1) := by
  have hd : 0 < d + 1 := by have := Nat.cast_nonneg (α := ℝ) p.natDegree; linarith
  have hM : (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ (d + 1) * Real.exp t := by
    calc
      _ ≤ (p.map (Int.castRingHom ℂ)).sum (fun _ a ↦ ‖a‖) :=
        mahlerMeasure_le_sum_norm_coeff _
      _ = ∑ k ∈ Finset.range (p.natDegree + 1), ‖((p.coeff k : ℤ) : ℂ)‖ := by
        rw [Polynomial.sum_over_range (h := fun _ ↦ norm_zero)]
        simp only [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int,
          coeff_map, Int.coe_castRingHom]
      _ ≤ ∑ _k ∈ Finset.range (p.natDegree + 1), Real.exp t := by
        apply Finset.sum_le_sum
        intro k _
        simpa using hcoeff k
      _ = (p.natDegree + 1 : ℝ) * Real.exp t := by simp
      _ ≤ (d + 1) * Real.exp t := by gcongr
  unfold logMeasure
  rw [logMahlerMeasure_eq_log_MahlerMeasure]
  calc
    _ ≤ Real.log ((d + 1) * Real.exp t) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (one_le_mahlerMeasure_of_ne_zero hp)) hM
    _ = t + Real.log (d + 1) := by
      rw [Real.log_mul hd.ne' (Real.exp_ne_zero _), Real.log_exp, add_comm]

lemma logMeasure_le_of_dvd {p q : ℤ[X]} (hp : p ≠ 0) (hqp : q ∣ p) :
    logMeasure q ≤ logMeasure p := by
  obtain ⟨r, rfl⟩ := hqp
  have hq := (mul_ne_zero_iff.mp hp).1
  have hr := (mul_ne_zero_iff.mp hp).2
  rw [logMeasure_mul hq hr]
  exact le_add_of_nonneg_right (logMeasure_nonneg hr)

lemma norm_aeval_eq_of_associated {p q : ℤ[X]} (hpq : Associated p q) (θ : ℂ) :
    ‖aeval θ p‖ = ‖aeval θ q‖ := by
  obtain ⟨u, rfl⟩ := hpq
  obtain ⟨a, ha, hua⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have habs : |a| = 1 := Int.isUnit_iff_abs_eq.mp ha
  rw [map_mul, norm_mul, ← hua]
  have har : |(a : ℝ)| = 1 := by exact_mod_cast habs
  simp [har]

lemma logValue_nonneg_of_natDegree_eq_zero {θ : ℂ} {p : ℤ[X]}
    (hp : p ≠ 0) (hdeg : p.natDegree = 0) : 0 ≤ logValue θ p := by
  obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hdeg
  have ha : a ≠ 0 := by simpa using hp
  apply Real.log_nonneg
  simpa [Int.cast_abs, Int.cast_le, logValue] using
    (show (1 : ℝ) ≤ |(a : ℝ)| by exact_mod_cast Int.one_le_abs ha)

/-- A strict small-value inequality passes to an irreducible factor because
both logarithmic value and the degree--Mahler weight are additive. -/
lemma exists_irreducible_factor_small
    (θ : ℂ) (d t k : ℝ) (hd : 0 ≤ d) (ht : 0 ≤ t) (hk : 0 ≤ k)
    (p : ℤ[X]) (hp : aeval θ p ≠ 0)
    (hsmall : logValue θ p < -k * weight d t p) :
    ∃ q : ℤ[X], Irreducible q ∧ q ∣ p ∧ 0 < q.natDegree ∧
      aeval θ q ≠ 0 ∧ logValue θ q < -k * weight d t q := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at hp
  | unit p hunit =>
      have hdeg : p.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
      have hv := logValue_nonneg_of_natDegree_eq_zero hunit.ne_zero hdeg (θ := θ)
      have hw := weight_nonneg hd ht hunit.ne_zero
      nlinarith
  | mul b a hb ha ih =>
      have hae : aeval θ a ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hp)).1
      have hbe : aeval θ b ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hp)).2
      have hb0 : b ≠ 0 := by intro h; simp [h] at hbe
      rw [logValue_mul hae hbe, weight_mul ha.ne_zero hb0] at hsmall
      by_cases hs : logValue θ a < -k * weight d t a
      · refine ⟨a, ha, dvd_mul_right a b, ?_, hae, hs⟩
        by_contra! hdeg
        have hv := logValue_nonneg_of_natDegree_eq_zero ha.ne_zero
          (Nat.eq_zero_of_le_zero hdeg) (θ := θ)
        have hw := weight_nonneg hd ht ha.ne_zero
        nlinarith
      · obtain ⟨q, hq, hqb, hqd, hqe, hqs⟩ := ih hbe (by linarith)
        exact ⟨q, hq, dvd_mul_of_dvd_right hqb a, hqd, hqe, hqs⟩

lemma exists_irreducible_factor_of_strong_smallness
    (θ : ℂ) (c d t : ℝ) (hc : 1 < c) (hd : 0 < d) (ht : 0 < t)
    (hlog : (c + 1) * Real.log (d + 1) ≤ d / 8)
    (p : ℤ[X]) (hp : aeval θ p ≠ 0)
    (hdeg : (p.natDegree : ℝ) ≤ d)
    (hcoeff : ∀ k, |(p.coeff k : ℝ)| ≤ Real.exp t)
    (hsmall : logValue θ p ≤ -(2 * c + 1) * d * (t + d)) :
    ∃ q : ℤ[X], Irreducible q ∧ q ∣ p ∧ 0 < q.natDegree ∧
      aeval θ q ≠ 0 ∧ logValue θ q < -(c + 1 / 4) * weight d t q := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have he : 0 ≤ Real.log (d + 1) := Real.log_nonneg (by linarith)
  have hM := logMeasure_le_of_coeff_bound hp0 hdeg hcoeff
  have hW : weight d t p ≤ 2 * d * (t + d) + d * Real.log (d + 1) := by
    unfold weight
    calc
      _ ≤ d * (t + 2 * d) + d * (t + Real.log (d + 1)) := by gcongr
      _ = _ := by ring
  have hk : 0 < c + 1 / 4 := by linarith
  have hke : (c + 1 / 4) * Real.log (d + 1) ≤ d / 8 := by
    exact (mul_le_mul_of_nonneg_right (by linarith) he).trans hlog
  have hslack : (c + 1 / 4) * weight d t p < (2 * c + 1) * d * (t + d) := by
    have hW' := mul_le_mul_of_nonneg_left hW hk.le
    have hke' := mul_le_mul_of_nonneg_left hke hd.le
    nlinarith [mul_pos hd ht, sq_pos_of_pos hd]
  exact exists_irreducible_factor_small θ d t (c + 1 / 4) hd.le ht.le hk.le p hp
    (by linarith)

end TranscendenceTheory.Gelfond

open Polynomial Matrix
open scoped Polynomial

namespace TranscendenceTheory.Gelfond

lemma norm_det_le_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A.det‖ ≤ ∏ j, ∑ i, ‖A i j‖ := by
  classical
  calc
    ‖A.det‖ ≤ ∑ σ : Equiv.Perm ι, ∏ j, ‖A (σ j) j‖ := by
      rw [Matrix.det_apply]
      calc
        _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ j, A (σ j) j‖ :=
          norm_sum_le _ _
        _ = _ := by
          congr 1
          ext σ
          simp [norm_prod]
    _ ≤ ∑ f : ι → ι, ∏ j, ‖A (f j) j‖ := by
      let e : Equiv.Perm ι ↪ (ι → ι) := ⟨(↑), fun _ _ h ↦ Equiv.ext (congrFun h)⟩
      calc
        _ = ∑ f ∈ Finset.univ.map e, ∏ j, ‖A (f j) j‖ := by
          simp only [Finset.sum_map]
          rfl
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ ↦ by positivity)
    _ = ∏ j, ∑ i, ‖A i j‖ := by
      symm
      exact Fintype.prod_sum _

lemma norm_det_le_row_bound {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (r : Fin (n + 1)) (B : Fin (n + 1) → ℝ) (ε : ℝ)
    (hB : ∀ j, 1 ≤ B j) (hε : 0 ≤ ε)
    (hr : ∀ j, ‖A r j‖ ≤ ε)
    (hcol : ∀ j, ∑ i : Fin n, ‖A (r.succAbove i) j‖ ≤ B j) :
    ‖A.det‖ ≤ (n + 1) * ε * ∏ j, B j := by
  classical
  rw [Matrix.det_succ_row A r]
  calc
    _ ≤ ∑ j : Fin (n + 1),
        ‖(-1 : ℂ) ^ (r + j : ℕ) * A r j *
          (A.submatrix r.succAbove j.succAbove).det‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (n + 1), ε * ∏ j, B j := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      apply mul_le_mul (hr j)
      · calc
          _ ≤ ∏ k : Fin n, ∑ i : Fin n, ‖A (r.succAbove i) (j.succAbove k)‖ :=
            norm_det_le_prod_sum _
          _ ≤ ∏ k : Fin n, B (j.succAbove k) :=
            Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun k _ ↦ hcol _)
          _ ≤ ∏ k : Fin (n + 1), B k := by
            rw [Fin.prod_univ_succAbove (f := B) j]
            exact le_mul_of_one_le_left
              (Finset.prod_nonneg (fun k _ ↦ (zero_le_one.trans (hB _)))) (hB j)
      · exact norm_nonneg _
      · exact hε
    _ = _ := by simp; ring

lemma norm_det_updateRow_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (r : Fin N) (u : Fin N → ℂ) (B : Fin N → ℝ) (ε : ℝ)
    (hB : ∀ j, 1 ≤ B j) (hε : 0 ≤ ε)
    (hu : ∀ j, ‖u j‖ ≤ ε) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ B j) :
    ‖(A.updateRow r u).det‖ ≤ N * ε * ∏ j, B j := by
  cases N with
  | zero => exact Fin.elim0 r
  | succ n =>
    simp only [Nat.cast_add, Nat.cast_one]
    apply norm_det_le_row_bound (A.updateRow r u) r B ε hB hε
    · simpa using hu
    · intro j
      have heq : ∀ i : Fin n, (A.updateRow r u) (r.succAbove i) j = A (r.succAbove i) j := by
        intro i
        rw [Matrix.updateRow_apply, if_neg (Fin.succAbove_ne r i)]
      simp_rw [heq]
      have h := hcol j
      rw [Fin.sum_univ_succAbove (fun i ↦ ‖A i j‖) r] at h
      linarith [norm_nonneg (A r j)]

lemma sum_norm_coeff_le_mahler (p : ℂ[X]) :
    p.sum (fun _ a ↦ ‖a‖) ≤ 2 ^ p.natDegree * p.mahlerMeasure := by
  rw [Polynomial.sum_over_range (h := fun _ ↦ norm_zero)]
  calc
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1),
        (p.natDegree.choose k : ℝ) * p.mahlerMeasure :=
      Finset.sum_le_sum (fun k _ ↦ norm_coeff_le_choose_mul_mahlerMeasure k p)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose p.natDegree

lemma sum_norm_coeff_shift (p : ℂ[X]) (j N : ℕ) (hj : j ≤ N)
    (hp : p.natDegree < N - j) :
    ∑ i : Fin N, ‖(p * X ^ j).coeff i‖ = p.sum (fun _ a ↦ ‖a‖) := by
  calc
    _ = ∑ i ∈ Finset.range N, ‖(p * X ^ j).coeff i‖ := by
      convert! Fin.sum_univ_eq_sum_range (fun i ↦ ‖(p * X ^ j).coeff i‖) N using 1
    _ = _ := ?_
  have hN : N = j + (N - j) := by omega
  rw [hN, Finset.sum_range_add]
  have hzero : ∑ i ∈ Finset.range j, ‖(p * X ^ j).coeff i‖ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [coeff_mul_X_pow', Nat.not_le.mpr (Finset.mem_range.mp hi)]
  rw [hzero, zero_add]
  simp only [coeff_mul_X_pow', Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
  exact (p.sum_over_range' (fun _ ↦ norm_zero) (N - j) hp).symm

lemma sylvester_apply_eq_coeff (f g : ℂ[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (i j : Fin (m + n)) :
    f.sylvester g m n i j = j.addCases
      (fun k ↦ (g * X ^ (k : ℕ)).coeff i)
      (fun k ↦ (f * X ^ (k : ℕ)).coeff i) := by
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, coeff_mul_X_pow', Set.mem_Icc]
    split_ifs with h₁ h₂ h₃
    · rfl
    · omega
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
    · rfl
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right, coeff_mul_X_pow', Set.mem_Icc]
    split_ifs with h₁ h₂ h₃
    · rfl
    · omega
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
    · rfl

lemma sylvester_col_norm (f g : ℂ[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (j : Fin (m + n)) :
    (∑ i : Fin (m + n), ‖f.sylvester g m n i j‖) ≤ j.addCases
      (fun _ ↦ 2 ^ g.natDegree * g.mahlerMeasure)
      (fun _ ↦ 2 ^ f.natDegree * f.mahlerMeasure) := by
  simp_rw [sylvester_apply_eq_coeff f g m n hf hg]
  induction j using Fin.addCases with
  | left j =>
    simp only [Fin.addCases_left]
    rw [sum_norm_coeff_shift g j (m + n) (by omega) (by omega)]
    exact sum_norm_coeff_le_mahler g
  | right j =>
    simp only [Fin.addCases_right]
    rw [sum_norm_coeff_shift f j (m + n) (by omega) (by omega)]
    exact sum_norm_coeff_le_mahler f

lemma sylvester_weighted_row (f g : ℂ[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (θ : ℂ) (j : Fin (m + n)) :
    (∑ i : Fin (m + n), θ ^ (i : ℕ) • f.sylvester g m n i) j =
      j.addCases (fun k ↦ g.eval θ * θ ^ (k : ℕ))
        (fun k ↦ f.eval θ * θ ^ (k : ℕ)) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [sylvester_apply_eq_coeff f g m n hf hg]
  induction j using Fin.addCases with
  | left j =>
    simp only [Fin.addCases_left]
    have hp : (g * X ^ (j : ℕ)).natDegree < m + n := by
      have := natDegree_mul_le (p := g) (q := (X : ℂ[X]) ^ (j : ℕ))
      simp only [natDegree_X_pow] at this
      omega
    calc
      _ = (g * X ^ (j : ℕ)).eval θ := by
        rw [eval_eq_sum_range' hp]
        convert! Fin.sum_univ_eq_sum_range
          (fun i ↦ (g * X ^ (j : ℕ)).coeff i * θ ^ i) (m + n) using 1
        simp only [mul_comm]
      _ = _ := by simp
  | right j =>
    simp only [Fin.addCases_right]
    have hp : (f * X ^ (j : ℕ)).natDegree < m + n := by
      have := natDegree_mul_le (p := f) (q := (X : ℂ[X]) ^ (j : ℕ))
      simp only [natDegree_X_pow] at this
      omega
    calc
      _ = (f * X ^ (j : ℕ)).eval θ := by
        rw [eval_eq_sum_range' hp]
        convert! Fin.sum_univ_eq_sum_range
          (fun i ↦ (f * X ^ (j : ℕ)).coeff i * θ ^ i) (m + n) using 1
        simp only [mul_comm]
      _ = _ := by simp

/-- A small-value bound for the Sylvester determinant on the closed unit disc. -/
lemma norm_resultant_le (f g : ℂ[X])
    (hm : 0 < f.natDegree) (hn : 0 < g.natDegree)
    (hf : 1 ≤ f.mahlerMeasure) (hg : 1 ≤ g.mahlerMeasure)
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ‖f.resultant g‖ ≤ ((f.natDegree + g.natDegree : ℕ) : ℝ) *
      max ‖f.eval θ‖ ‖g.eval θ‖ *
      ((2 ^ g.natDegree * g.mahlerMeasure) ^ f.natDegree *
       (2 ^ f.natDegree * f.mahlerMeasure) ^ g.natDegree) := by
  classical
  let m := f.natDegree
  let n := g.natDegree
  let : NeZero (m + n) := ⟨by dsimp [m, n]; omega⟩
  let A := f.sylvester g m n
  let u := ∑ i : Fin (m + n), θ ^ (i : ℕ) • A i
  let B : Fin (m + n) → ℝ := fun j ↦ j.addCases
    (fun _ ↦ 2 ^ n * g.mahlerMeasure) (fun _ ↦ 2 ^ m * f.mahlerMeasure)
  have hB : ∀ j, 1 ≤ B j := by
    intro j
    induction j using Fin.addCases with
    | left j =>
      simp only [B, Fin.addCases_left]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hg
    | right j =>
      simp only [B, Fin.addCases_right]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hf
  have hu : ∀ j, ‖u j‖ ≤ max ‖f.eval θ‖ ‖g.eval θ‖ := by
    intro j
    dsimp [u, A]
    rw [sylvester_weighted_row f g m n le_rfl le_rfl]
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.addCases_left, norm_mul, norm_pow]
      calc
        _ ≤ ‖g.eval θ‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hθ
        _ ≤ _ := by simp only [mul_one]; exact le_max_right _ _
    | right j =>
      simp only [Fin.addCases_right, norm_mul, norm_pow]
      calc
        _ ≤ ‖f.eval θ‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hθ
        _ ≤ _ := by simp only [mul_one]; exact le_max_left _ _
  have hd : (A.updateRow 0 u).det = A.det := by
    simpa [u] using Matrix.det_updateRow_sum A (0 : Fin (m + n)) (fun i ↦ θ ^ (i : ℕ))
  have h := norm_det_updateRow_le A 0 u B (max ‖f.eval θ‖ ‖g.eval θ‖) hB
    (le_trans (norm_nonneg _) (le_max_left _ _)) hu
    (sylvester_col_norm f g m n le_rfl le_rfl)
  rw [hd] at h
  simpa [Polynomial.resultant, A, B, Fin.prod_univ_add, m, n] using h
end TranscendenceTheory.Gelfond

open Filter
open scoped Topology

namespace TranscendenceTheory.Gelfond

lemma eventually_mul_log_linear_le (C K : ℝ) (hC : 0 < C) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, K * Real.log (C * x + 1) ≤ x := by
  have hε : 0 < 1 / (2 * K * C) := by positivity
  have hlim : Tendsto (fun x : ℝ ↦ C * x + 1) atTop atTop :=
    tendsto_atTop_mono (fun x ↦ by linarith : ∀ x : ℝ, C * x ≤ C * x + 1)
      (tendsto_id.const_mul_atTop hC)
  have hl := hlim.eventually (Real.isLittleO_log_id_atTop.bound hε)
  filter_upwards [hl, eventually_ge_atTop (1 / C)] with x hx hxl
  have hxpos : 0 < x := (div_pos zero_lt_one hC).trans_le hxl
  have hCx : 1 ≤ C * x := by nlinarith [(div_le_iff₀ hC).mp hxl]
  have hpos : 0 < C * x + 1 := by positivity
  have hlogpos : 0 ≤ Real.log (C * x + 1) := Real.log_nonneg (by linarith)
  simp only [id_eq, Real.norm_eq_abs,
    abs_of_nonneg hlogpos, abs_of_pos hpos] at hx
  have hscaled := mul_le_mul_of_nonneg_left hx (le_of_lt hK)
  have hcancel : K * (1 / (2 * K * C) * (C * x + 1)) =
      (C * x + 1) / (2 * C) := by field_simp
  rw [hcancel] at hscaled
  exact hscaled.trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith))

lemma resultant_exponent_lt_weight
    (c d t a b u v e ℓ : ℝ) (_hc : 1 < c) (hd : 0 < d) (ht : 0 < t)
    (ha : 1 ≤ a) (_hb : 0 ≤ b) (hbd : b ≤ c * d)
    (hu : 0 ≤ u) (hv : v ≤ c * t + e)
    (he : 0 ≤ e) (hed : e ≤ d / 8) (hℓ : ℓ ≤ e) :
    ℓ + 2 * a * b + b * u + a * v <
      (c + 1 / 4) * (a * (t + 2 * d) + d * u) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hw : a * d < a * (t + 2 * d) + d * u := by
    nlinarith [mul_pos ha0 ht, mul_pos ha0 hd, mul_nonneg hd.le hu]
  have herr : (a + 1) * e ≤ a * d / 4 := by
    calc
      _ ≤ (2 * a) * (d / 8) :=
        mul_le_mul (by linarith) hed he (by positivity)
      _ = _ := by ring
  calc
    _ ≤ e + 2 * a * (c * d) + (c * d) * u + a * (c * t + e) := by
      gcongr
    _ = c * (a * (t + 2 * d) + d * u) + (a + 1) * e := by ring
    _ ≤ c * (a * (t + 2 * d) + d * u) + a * d / 4 := by linarith
    _ < _ := by nlinarith

end TranscendenceTheory.Gelfond

open Polynomial
open scoped Polynomial

namespace TranscendenceTheory.Gelfond

lemma resultant_ne_zero_of_not_associated {p q : ℤ[X]}
    (hp : Irreducible p) (hq : Irreducible q)
    (hpdeg : 0 < p.natDegree) (hqdeg : 0 < q.natDegree)
    (hpq : ¬Associated p q) : p.resultant q ≠ 0 := by
  have hpprim := hp.isPrimitive hpdeg.ne'
  have hqprim := hq.isPrimitive hqdeg.ne'
  have hpQ : Irreducible (p.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hpprim).mp hp
  have hcop : IsCoprime (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ)) := by
    apply (hpQ.isCoprime_or_dvd _).resolve_right
    intro h
    have hpq' : p ∣ q := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast p q hpprim).mpr h
    exact hpq (associated_of_dvd_dvd hpq' (hp.dvd_symm hq hpq'))
  have h := resultant_ne_zero _ _ hcop
  simpa [natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int,
    resultant_map_map] using h

lemma logValue_lower_bound_of_not_associated {p q : ℤ[X]}
    (hp : Irreducible p) (hq : Irreducible q)
    (hpdeg : 0 < p.natDegree) (hqdeg : 0 < q.natDegree)
    (hpq : ¬Associated p q) (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (hpe : aeval θ p ≠ 0) (hqe : aeval θ q ≠ 0) :
    -(Real.log (p.natDegree + q.natDegree : ℝ) +
      2 * p.natDegree * q.natDegree + q.natDegree * logMeasure p +
      p.natDegree * logMeasure q) ≤ max (logValue θ p) (logValue θ q) := by
  let f := p.map (Int.castRingHom ℂ)
  let g := q.map (Int.castRingHom ℂ)
  have hfd : f.natDegree = p.natDegree := natDegree_map_eq_of_injective
    (Int.castRingHom ℂ).injective_int p
  have hgd : g.natDegree = q.natDegree := natDegree_map_eq_of_injective
    (Int.castRingHom ℂ).injective_int q
  have hfe : f.eval θ = aeval θ p := by dsimp [f]; rw [eval_map]; rfl
  have hge : g.eval θ = aeval θ q := by dsimp [g]; rw [eval_map]; rfl
  have hfM := one_le_mahlerMeasure_of_ne_zero hp.ne_zero
  have hgM := one_le_mahlerMeasure_of_ne_zero hq.ne_zero
  have hfM0 : 0 < f.mahlerMeasure := zero_lt_one.trans_le hfM
  have hgM0 : 0 < g.mahlerMeasure := zero_lt_one.trans_le hgM
  have hres : 1 ≤ ‖f.resultant g‖ := by
    have h := resultant_ne_zero_of_not_associated hp hq hpdeg hqdeg hpq
    have h' : (1 : ℝ) ≤ |(p.resultant q : ℝ)| := by exact_mod_cast Int.one_le_abs h
    simpa [f, g, natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int,
      resultant_map_map] using h'
  have hbound := norm_resultant_le f g (by simpa [hfd] using hpdeg)
    (by simpa [hgd] using hqdeg) hfM hgM θ hθ
  have hN : 0 < (p.natDegree + q.natDegree : ℝ) := by positivity
  have hV : 0 < max ‖aeval θ p‖ ‖aeval θ q‖ :=
    (norm_pos_iff.mpr hpe).trans_le (le_max_left _ _)
  have hlog := Real.log_nonneg (hres.trans hbound)
  rw [hfd, hgd, hfe, hge] at hlog
  simp only [Nat.cast_add] at hlog
  have hA : 0 < 2 ^ q.natDegree * g.mahlerMeasure := by positivity
  have hB : 0 < 2 ^ p.natDegree * f.mahlerMeasure := by positivity
  rw [Real.log_mul (mul_pos hN hV).ne' (mul_pos (pow_pos hA _) (pow_pos hB _)).ne',
    Real.log_mul hN.ne' hV.ne', Real.log_mul (pow_pos hA _).ne' (pow_pos hB _).ne',
    Real.log_pow, Real.log_pow] at hlog
  rw [Real.log_mul (by positivity) hgM0.ne', Real.log_mul (by positivity) hfM0.ne',
    Real.log_pow, Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmax : Real.log (max ‖aeval θ p‖ ‖aeval θ q‖) =
      max (logValue θ p) (logValue θ q) := by
    unfold logValue
    rcases le_total ‖aeval θ p‖ ‖aeval θ q‖ with h | h
    · rw [max_eq_right h, max_eq_right (Real.log_le_log (norm_pos_iff.mpr hpe) h)]
    · rw [max_eq_left h, max_eq_left (Real.log_le_log (norm_pos_iff.mpr hqe) h)]
  rw [hmax] at hlog
  have hfLM : Real.log f.mahlerMeasure = logMeasure p :=
    f.logMahlerMeasure_eq_log_MahlerMeasure.symm
  have hgLM : Real.log g.mahlerMeasure = logMeasure q :=
    g.logMahlerMeasure_eq_log_MahlerMeasure.symm
  rw [hfLM, hgLM] at hlog
  nlinarith [mul_le_mul_of_nonneg_left hlog2
    (show (0 : ℝ) ≤ 2 * p.natDegree * q.natDegree by positivity)]

lemma associated_of_two_small_values {p q : ℤ[X]}
    (hp : Irreducible p) (hq : Irreducible q)
    (hpdeg : 0 < p.natDegree) (hqdeg : 0 < q.natDegree)
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (hpe : aeval θ p ≠ 0) (hqe : aeval θ q ≠ 0)
    (c d t D T e : ℝ) (hc : 1 < c)
    (hd : 0 < d) (ht : 0 < t) (hD : d ≤ D) (hT : t ≤ T)
    (hDgrowth : D ≤ c * d) (hTgrowth : T ≤ c * t)
    (hpd : (p.natDegree : ℝ) ≤ d) (hqd : (q.natDegree : ℝ) ≤ D)
    (hpM : logMeasure p ≤ t + e) (hqM : logMeasure q ≤ T + e)
    (he : 0 ≤ e) (hed : e ≤ d / 8)
    (hℓ : Real.log (p.natDegree + q.natDegree : ℝ) ≤ e)
    (hpv : logValue θ p < -(c + 1 / 4) * weight d t p)
    (hqv : logValue θ q < -(c + 1 / 4) * weight D T q) : Associated p q := by
  by_contra hnot
  let E := Real.log (p.natDegree + q.natDegree : ℝ) +
    2 * p.natDegree * q.natDegree + q.natDegree * logMeasure p +
    p.natDegree * logMeasure q
  have hpa : (1 : ℝ) ≤ p.natDegree := by exact_mod_cast hpdeg
  have hqa : (1 : ℝ) ≤ q.natDegree := by exact_mod_cast hqdeg
  have hpM0 := logMeasure_nonneg hp.ne_zero
  have hqM0 := logMeasure_nonneg hq.ne_zero
  have hDpos : 0 < D := hd.trans_le hD
  have hTpos : 0 < T := ht.trans_le hT
  have hleft : E < (c + 1 / 4) * weight d t p := by
    exact resultant_exponent_lt_weight c d t p.natDegree q.natDegree
      (logMeasure p) (logMeasure q) e _ hc hd ht hpa (by positivity)
      (hqd.trans hDgrowth) hpM0 (by linarith) he hed hℓ
  have hright : E < (c + 1 / 4) * weight D T q := by
    have hpd' : (p.natDegree : ℝ) ≤ c * D := by
      have := mul_le_mul_of_nonneg_right hc.le hDpos.le
      linarith
    have hpM' : logMeasure p ≤ c * T + e := by
      have := mul_le_mul_of_nonneg_right hc.le hTpos.le
      linarith
    have h := resultant_exponent_lt_weight c D T q.natDegree p.natDegree
      (logMeasure q) (logMeasure p) e _ hc hDpos hTpos hqa (by positivity)
      hpd' hqM0 hpM' he (by linarith) hℓ
    convert! h using 1
    dsimp [E, weight]
    ring
  have hlow : -E ≤ max (logValue θ p) (logValue θ q) :=
    logValue_lower_bound_of_not_associated hp hq hpdeg hqdeg hnot θ hθ hpe hqe
  have hsmall : max (logValue θ p) (logValue θ q) < -E :=
    max_lt (by linarith) (by linarith)
  linarith

end TranscendenceTheory.Gelfond

open Filter Polynomial
open scoped Topology Polynomial

namespace TranscendenceTheory.Gelfond

lemma no_small_sequence_in_disc
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1) (c : ℝ) (hc : 1 < c) (d t : ℕ → ℝ)
    (hd : ∀ n, 0 < d n) (ht : ∀ n, 0 < t n)
    (hd_mono : Monotone d) (ht_mono : Monotone t)
    (ht_unbounded : Tendsto t atTop atTop)
    (hd_growth : ∀ n, d (n + 1) ≤ c * d n)
    (ht_growth : ∀ n, t (n + 1) ≤ c * t n)
    (hlarge : ∀ n, 8 * (c + 1) * Real.log ((c + 1) * d n + 1) ≤ d n)
    (P : ℕ → ℤ[X]) (hP : ∀ n, aeval θ (P n) ≠ 0)
    (hdeg : ∀ n, ((P n).natDegree : ℝ) ≤ d n)
    (hcoeff : ∀ n k, |((P n).coeff k : ℝ)| ≤ Real.exp (t n))
    (hsmall : ∀ n, logValue θ (P n) ≤ -(2 * c + 1) * d n * (t n + d n)) :
    False := by
  classical
  have hc0 : 0 < c := by linarith
  have hk : 0 < c + 1 / 4 := by linarith
  have hP0 : ∀ n, P n ≠ 0 := by
    intro n h
    have hpn := hP n
    simp [h] at hpn
  have hlog (n : ℕ) : (c + 1) * Real.log (d n + 1) ≤ d n / 8 := by
    have hle : Real.log (d n + 1) ≤ Real.log ((c + 1) * d n + 1) := by
      apply Real.log_le_log (by linarith [hd n])
      nlinarith [hd n]
    have h := mul_le_mul_of_nonneg_left hle (by linarith : 0 ≤ c + 1)
    nlinarith [hlarge n]
  have hex (n : ℕ) := exists_irreducible_factor_of_strong_smallness θ c (d n) (t n)
    hc (hd n) (ht n) (hlog n) (P n) (hP n) (hdeg n) (hcoeff n) (hsmall n)
  choose Q hQirr hQdvd hQdeg hQeval hQsmall using hex
  have hQd (n : ℕ) : ((Q n).natDegree : ℝ) ≤ d n := by
    have h := natDegree_le_of_dvd (hQdvd n) (hP0 n)
    exact (by exact_mod_cast h : ((Q n).natDegree : ℝ) ≤ (P n).natDegree).trans (hdeg n)
  have hQM (n : ℕ) : logMeasure (Q n) ≤ t n + Real.log (d n + 1) :=
    (logMeasure_le_of_dvd (hP0 n) (hQdvd n)).trans
      (logMeasure_le_of_coeff_bound (hP0 n) (hdeg n) (hcoeff n))
  have hassoc (n : ℕ) : Associated (Q n) (Q (n + 1)) := by
    let e := Real.log ((c + 1) * d n + 1)
    have he : 0 ≤ e := Real.log_nonneg (by nlinarith [hd n])
    have hed : e ≤ d n / 8 := by
      have := hlarge n
      dsimp [e] at he ⊢
      nlinarith [mul_nonneg hc0.le he]
    have hprev : Real.log (d n + 1) ≤ e := by
      apply Real.log_le_log (by linarith [hd n])
      nlinarith [hd n]
    have hnext : Real.log (d (n + 1) + 1) ≤ e := by
      apply Real.log_le_log (by linarith [hd (n + 1)])
      nlinarith [hd n, hd_growth n]
    have hℓ : Real.log ((Q n).natDegree + (Q (n + 1)).natDegree : ℝ) ≤ e := by
      apply Real.log_le_log (add_pos
        (by exact_mod_cast hQdeg n) (by exact_mod_cast hQdeg (n + 1)))
      nlinarith [hQd n, hQd (n + 1), hd_growth n, hd n]
    exact associated_of_two_small_values (hQirr n) (hQirr (n + 1))
      (hQdeg n) (hQdeg (n + 1)) θ hθ (hQeval n) (hQeval (n + 1))
      c (d n) (t n) (d (n + 1)) (t (n + 1)) e hc (hd n) (ht n)
      (hd_mono (Nat.le_succ n)) (ht_mono (Nat.le_succ n)) (hd_growth n) (ht_growth n)
      (hQd n) (hQd (n + 1)) (by linarith [hQM n]) (by linarith [hQM (n + 1)])
      he hed hℓ (hQsmall n) (hQsmall (n + 1))
  have hconst : ∀ n, logValue θ (Q n) = logValue θ (Q 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (congrArg Real.log (norm_aeval_eq_of_associated (hassoc n) θ).symm).trans ih
  obtain ⟨n, hn⟩ := (ht_unbounded.eventually
    (eventually_ge_atTop ((-logValue θ (Q 0) + 1) / (c + 1 / 4)))).exists
  have hweight : t n ≤ weight (d n) (t n) (Q n) := by
    have ha : (1 : ℝ) ≤ (Q n).natDegree := by exact_mod_cast hQdeg n
    have hM := logMeasure_nonneg (hQirr n).ne_zero
    unfold weight
    nlinarith [mul_nonneg (hd n).le hM, mul_nonneg (hd n).le
      (show (0 : ℝ) ≤ (Q n).natDegree by positivity), ht n,
      mul_le_mul_of_nonneg_right ha (ht n).le]
  have hs := hQsmall n
  rw [hconst n] at hs
  have hw := mul_le_mul_of_nonneg_left hweight hk.le
  have htn := (div_le_iff₀ hk).mp hn
  nlinarith

lemma polynomial_sequence_lower_bound_in_disc
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1) (c : ℝ) (hc : 1 < c) (d t : ℕ → ℝ)
    (hd : ∀ n, 0 < d n) (ht : ∀ n, 0 < t n)
    (hd_mono : Monotone d) (ht_mono : Monotone t)
    (hd_unbounded : Tendsto d atTop atTop) (ht_unbounded : Tendsto t atTop atTop)
    (hd_growth : ∀ n, d (n + 1) ≤ c * d n)
    (ht_growth : ∀ n, t (n + 1) ≤ c * t n)
    (P : ℕ → ℤ[X]) (hP : ∀ n, aeval θ (P n) ≠ 0)
    (hdeg : ∀ n, ((P n).natDegree : ℝ) ≤ d n)
    (hcoeff : ∀ n k, |((P n).coeff k : ℝ)| ≤ Real.exp (t n)) :
    ∃ᶠ n in atTop, -(2 * c + 1) * d n * (t n + d n) < logValue θ (P n) := by
  by_contra h
  have hs : ∀ᶠ n in atTop, logValue θ (P n) ≤ -(2 * c + 1) * d n * (t n + d n) := by
    simpa only [not_lt] using not_frequently.mp h
  have hl := hd_unbounded.eventually
    (eventually_mul_log_linear_le (c + 1) (8 * (c + 1)) (by linarith) (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.and hl)
  apply no_small_sequence_in_disc θ hθ c hc (fun n ↦ d (n + N)) (fun n ↦ t (n + N))
    (fun n ↦ hd _) (fun n ↦ ht _)
    (fun i j hij ↦ hd_mono (Nat.add_le_add_right hij N))
    (fun i j hij ↦ ht_mono (Nat.add_le_add_right hij N))
    (ht_unbounded.comp (tendsto_add_atTop_nat N))
    (fun n ↦ by simpa [Nat.add_right_comm] using hd_growth (n + N))
    (fun n ↦ by simpa [Nat.add_right_comm] using ht_growth (n + N))
    (fun n ↦ (hN (n + N) (by omega)).2) (fun n ↦ P (n + N))
    (fun n ↦ hP _) (fun n ↦ hdeg _) (fun n k ↦ hcoeff _ k)
    (fun n ↦ (hN (n + N) (by omega)).1)

lemma aeval_reverse_mul_pow (θ : ℂ) (hθ : θ ≠ 0) (p : ℤ[X]) :
    aeval θ⁻¹ p.reverse * θ ^ p.natDegree = aeval θ p := by
  let := invertibleOfNonzero hθ
  convert! Polynomial.eval₂_reverse_mul_pow (Int.castRingHom ℂ) θ p using 1

lemma polynomial_sequence_lower_bound
    (θ : ℂ) (c : ℝ) (hc : 1 < c) (d t : ℕ → ℝ)
    (hd : ∀ n, 0 < d n) (ht : ∀ n, 0 < t n)
    (hd_mono : Monotone d) (ht_mono : Monotone t)
    (hd_unbounded : Tendsto d atTop atTop) (ht_unbounded : Tendsto t atTop atTop)
    (hd_growth : ∀ n, d (n + 1) ≤ c * d n)
    (ht_growth : ∀ n, t (n + 1) ≤ c * t n)
    (P : ℕ → ℤ[X]) (hP : ∀ n, aeval θ (P n) ≠ 0)
    (hdeg : ∀ n, ((P n).natDegree : ℝ) ≤ d n)
    (hcoeff : ∀ n k, |((P n).coeff k : ℝ)| ≤ Real.exp (t n)) :
    ∃ᶠ n in atTop, -(2 * c + 1) * d n * (t n + d n) < logValue θ (P n) := by
  by_cases hdisc : ‖θ‖ ≤ 1
  · exact polynomial_sequence_lower_bound_in_disc θ hdisc c hc d t hd ht hd_mono ht_mono
      hd_unbounded ht_unbounded hd_growth ht_growth P hP hdeg hcoeff
  have hθnorm : 1 < ‖θ‖ := lt_of_not_ge hdisc
  have hθ : θ ≠ 0 := by intro h; norm_num [h] at hθnorm
  have hinv : ‖θ⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hθnorm.le
  have hrev (n : ℕ) : aeval θ⁻¹ (P n).reverse ≠ 0 := by
    intro h
    have heq := aeval_reverse_mul_pow θ hθ (P n)
    rw [h, zero_mul] at heq
    exact hP n heq.symm
  have hrevdeg (n : ℕ) : ((P n).reverse.natDegree : ℝ) ≤ d n := by
    have h : ((P n).reverse.natDegree : ℝ) ≤ (P n).natDegree := by
      exact_mod_cast (P n).reverse_natDegree_le
    exact h.trans (hdeg n)
  have hrevcoeff (n k : ℕ) : |((P n).reverse.coeff k : ℝ)| ≤ Real.exp (t n) := by
    rw [coeff_reverse]
    exact hcoeff n _
  have hfreq := polynomial_sequence_lower_bound_in_disc θ⁻¹ hinv c hc d t hd ht
    hd_mono ht_mono hd_unbounded ht_unbounded hd_growth ht_growth
    (fun n ↦ (P n).reverse) hrev hrevdeg hrevcoeff
  apply hfreq.mono
  intro n hn
  apply hn.trans_le
  apply Real.log_le_log (norm_pos_iff.mpr (hrev n))
  have heq := congrArg norm (aeval_reverse_mul_pow θ hθ (P n))
  simp only [norm_mul, norm_pow] at heq
  rw [← heq]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hθnorm.le)

end TranscendenceTheory.Gelfond

theorem solution
    (θ : ℂ) (hθ : Transcendental ℚ θ) (c : ℝ) (hc : 1 < c)
    (d t : ℕ → ℝ)
    (hd_pos : ∀ n, 0 < d n) (ht_pos : ∀ n, 0 < t n)
    (hd_strict : StrictMono d) (ht_strict : StrictMono t)
    (hd_unbounded : Tendsto d atTop atTop) (ht_unbounded : Tendsto t atTop atTop)
    (hd_growth : ∀ n, d (n + 1) ≤ c * d n)
    (ht_growth : ∀ n, t (n + 1) ≤ c * t n)
    (P : ℕ → ℤ[X])
    (h_nonzero : ∀ n, Polynomial.aeval θ (P n) ≠ 0)
    (h_degree : ∀ n, ((P n).natDegree : ℝ) ≤ d n)
    (h_coeff : ∀ n k, |((P n).coeff k : ℝ)| ≤ Real.exp (t n)) :
    ∃ᶠ n in atTop,
      -(2 * c + 1) * d n * (t n + d n) <
        Real.log ‖Polynomial.aeval θ (P n)‖ := by
  clear hθ
  exact TranscendenceTheory.Gelfond.polynomial_sequence_lower_bound θ c hc d t
    hd_pos ht_pos hd_strict.monotone ht_strict.monotone hd_unbounded ht_unbounded
    hd_growth ht_growth P h_nonzero h_degree h_coeff
