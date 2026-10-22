-- Prove2me | solution 1 for SlowConvergence.Newton.third_deriv_along_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:52:14.065302+00:00
-- url     : https://prove2.me/submissions/e840b1f6-b418-43e2-9964-5161fe91ee12

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

set_option autoImplicit false
open scoped RealInnerProductSpace
open SlowConvergence.Newton

lemma y_poly5_deriv (c0 c1 c2 c3 c4 c5 : ℝ) :
    deriv (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 + c5 * t ^ 5) =
      fun t => c1 + (2 * c2) * t + (3 * c3) * t ^ 2 + (4 * c4) * t ^ 3 + (5 * c5) * t ^ 4
        + 0 * t ^ 5 := by
  funext t
  rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop)]
  simp
  ring

lemma y_poly5_third (c0 c1 c2 c3 c4 c5 t : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 + c5 * t ^ 5) t
      = 6 * c3 + 24 * c4 * t + 60 * c5 * t ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
    y_poly5_deriv, y_poly5_deriv, y_poly5_deriv]
  simp
  ring

lemma y_eta_pos {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) : 0 < eta τ := by
  unfold eta
  apply div_pos h0; linarith

lemma y_mu_pos (τ : ℝ) (k : ℕ) : 0 < mu τ k := by
  unfold mu
  exact Real.rpow_pos_of_pos (by positivity) _

lemma y_base_le_one (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma y_mu_le_one {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (k : ℕ) : mu τ k ≤ 1 := by
  unfold mu
  have := y_eta_pos h0 h1
  exact Real.rpow_le_one (by positivity) (y_base_le_one k) (by linarith)

lemma y_phi_abs {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (k : ℕ) : |phi τ k| ≤ 1 := by
  have hη := y_eta_pos h0 h1
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hψ0 : 0 < SlowConvergence.SteepestDescent.psi τ k := by
    unfold SlowConvergence.SteepestDescent.psi
    exact Real.rpow_pos_of_pos (by positivity) _
  have hψ1 : SlowConvergence.SteepestDescent.psi τ k < 1 := by
    unfold SlowConvergence.SteepestDescent.psi
    exact Real.rpow_lt_one (by positivity) (by rw [div_lt_one (by positivity)]; linarith) (by linarith)
  unfold phi
  rw [abs_neg, abs_of_pos hψ0]; exact hψ1.le

lemma y_p_third_bound {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (k : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |iteratedDeriv 3 (p τ k) (t * mu τ k) * mu τ k ^ 3| ≤ 36 := by
  have hμ := y_mu_pos τ k
  have hμ1 := y_mu_le_one h0 h1 k
  have hφ := y_phi_abs h0 h1 k
  have hp : p τ k = fun t : ℝ =>
      (1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ))
        + (-mu τ k) * t + 1 / 2 * t ^ 2
        + (-4 * phi τ k / mu τ k) * t ^ 3
        + (7 * phi τ k / mu τ k ^ 2) * t ^ 4
        + (-3 * phi τ k / mu τ k ^ 3) * t ^ 5 := by
    funext t; rfl
  rw [hp, y_poly5_third]
  have e : (6 * (-4 * phi τ k / mu τ k) + 24 * (7 * phi τ k / mu τ k ^ 2) * (t * mu τ k)
      + 60 * (-3 * phi τ k / mu τ k ^ 3) * (t * mu τ k) ^ 2) * mu τ k ^ 3
      = phi τ k * mu τ k ^ 2 * (-24 + 168 * t - 180 * t ^ 2) := by
    field_simp
    ring
  rw [e, abs_mul, abs_mul]
  have h1 : |-24 + 168 * t - 180 * t ^ 2| ≤ 36 := by
    rw [abs_le]; constructor <;> nlinarith
  have h2 : |mu τ k ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  calc |phi τ k| * |mu τ k ^ 2| * |-24 + 168 * t - 180 * t ^ 2| ≤ 1 * 1 * 36 := by
        apply mul_le_mul (mul_le_mul hφ h2 (abs_nonneg _) (by norm_num)) h1 (abs_nonneg _) (by norm_num)
    _ = 36 := by norm_num

lemma y_q_third_bound (k : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |iteratedDeriv 3 (q k) t| ≤ 429 := by
  have hq : q k = fun t : ℝ =>
      (1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2)
        + (-((1 / ((k : ℝ) + 1)) ^ 2)) * t + (1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2) * t ^ 2
        + (1 / 2 * (9 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2)) * t ^ 3
        + (1 / 2 * (-16 * (1 / ((k : ℝ) + 2)) ^ 2 + 2 * (1 / ((k : ℝ) + 1)) ^ 2)) * t ^ 4
        + (1 / 2 * (7 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2)) * t ^ 5 := by
    funext t; rfl
  rw [hq, y_poly5_third]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hb0 : 0 ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by positivity
  have ha0 : 0 ≤ (1 / ((k : ℝ) + 2)) ^ 2 := by positivity
  have hb1 : (1 / ((k : ℝ) + 1)) ^ 2 ≤ 1 := by
    have := y_base_le_one k
    have h0 : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
    nlinarith
  have ha1 : (1 / ((k : ℝ) + 2)) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ 1 / ((k : ℝ) + 2) := by positivity
    have : 1 / ((k : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  set A := (1 / ((k : ℝ) + 2)) ^ 2
  set B := (1 / ((k : ℝ) + 1)) ^ 2
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ht2' : 0 ≤ t ^ 2 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg ht0 ha0, mul_nonneg ht0 hb0, mul_nonneg ht2' ha0, mul_nonneg ht2' hb0,
    mul_nonneg ht0 (sub_nonneg.mpr ht1), mul_nonneg ht2' (sub_nonneg.mpr ha1), mul_nonneg ht2' (sub_nonneg.mpr hb1),
    mul_nonneg (sub_nonneg.mpr ht2) ha0, mul_nonneg (sub_nonneg.mpr ht2) hb0,
    mul_nonneg (sub_nonneg.mpr ht1) ha0, mul_nonneg (sub_nonneg.mpr ht1) hb0,
    mul_nonneg ht0 (sub_nonneg.mpr ha1), mul_nonneg ht0 (sub_nonneg.mpr hb1)]

lemma y_sk_ge_one (τ : ℝ) (k : ℕ) : 1 ≤ ‖sk τ k‖ ^ 3 := by
  have hsk : sk τ k = !₂[mu τ k, 1] := by
    unfold sk; simp [xk]
  have h1 : (1 : ℝ) ≤ ‖sk τ k‖ := by
    rw [hsk, EuclideanSpace.norm_eq]
    rw [Real.one_le_sqrt]
    simp [Fin.sum_univ_two]
    positivity
  exact one_le_pow₀ h1

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv 3 (p τ k) (t * mu τ k) * mu τ k ^ 3 + iteratedDeriv 3 (q k) t|
          / ‖sk τ k‖ ^ 3 ≤ 858 := by
  intro t ht
  have h1 := y_p_third_bound hτ0 hτ1 k t ht.1 ht.2
  have h2 := y_q_third_bound k t ht.1 ht.2
  have h3 := y_sk_ge_one τ k
  have h4 : |iteratedDeriv 3 (p τ k) (t * mu τ k) * mu τ k ^ 3 + iteratedDeriv 3 (q k) t| ≤ 858 := by
    calc _ ≤ |iteratedDeriv 3 (p τ k) (t * mu τ k) * mu τ k ^ 3| + |iteratedDeriv 3 (q k) t| := abs_add_le _ _
      _ ≤ 858 := by linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg (iteratedDeriv 3 (p τ k) (t * mu τ k) * mu τ k ^ 3 + iteratedDeriv 3 (q k) t)]
