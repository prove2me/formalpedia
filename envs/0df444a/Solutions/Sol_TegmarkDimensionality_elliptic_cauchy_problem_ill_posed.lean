-- Prove2me | solution 1 for TegmarkDimensionality.elliptic_cauchy_problem_ill_posed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:04:16.949982+00:00
-- url     : https://prove2.me/submissions/9333ef96-981e-4ada-b292-1f7206322b24

import Mathlib

set_option autoImplicit false

lemma f3bf_dx1 (c b : ℝ) :
    deriv (fun x => Real.cos (c * x) * b / c) = fun x => -(Real.sin (c * x) * c) * b / c := by
  funext x
  have h : HasDerivAt (fun x => Real.cos (c * x) * b / c) (-(Real.sin (c * x) * c) * b / c) x := by
    have := ((((hasDerivAt_id' x).const_mul c).cos).mul_const b).div_const c
    exact this.congr_deriv (by ring)
  exact h.deriv

lemma f3bf_dx2 (c b : ℝ) :
    deriv (fun x => -(Real.sin (c * x) * c) * b / c) = fun x => -(Real.cos (c * x) * c * c) * b / c := by
  funext x
  have h : HasDerivAt (fun x => -(Real.sin (c * x) * c) * b / c)
      (-(Real.cos (c * x) * c * c) * b / c) x := by
    have := (((((hasDerivAt_id' x).const_mul c).sin).mul_const c).neg.mul_const b).div_const c
    exact this.congr_deriv (by ring)
  exact h.deriv

lemma f3bf_dy1 (c a : ℝ) :
    deriv (fun y => a * Real.cosh (c * y) / c) = fun y => a * (Real.sinh (c * y) * c) / c := by
  funext y
  have h : HasDerivAt (fun y => a * Real.cosh (c * y) / c) (a * (Real.sinh (c * y) * c) / c) y := by
    have := ((((hasDerivAt_id' y).const_mul c).cosh).const_mul a).div_const c
    exact this.congr_deriv (by ring)
  exact h.deriv

lemma f3bf_dy2 (c a : ℝ) :
    deriv (fun y => a * (Real.sinh (c * y) * c) / c) = fun y => a * (Real.cosh (c * y) * c * c) / c := by
  funext y
  have h : HasDerivAt (fun y => a * (Real.sinh (c * y) * c) / c)
      (a * (Real.cosh (c * y) * c * c) / c) y := by
    have := (((((hasDerivAt_id' y).const_mul c).sinh).mul_const c).const_mul a).div_const c
    exact this.congr_deriv (by ring)
  exact h.deriv

lemma f3bf_cosh_ge (t : ℝ) : t ^ 2 / 4 ≤ Real.cosh t := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
  have h2 := Real.exp_pos (-|t|)
  have h3 : |t| ^ 2 = t ^ 2 := sq_abs t
  have h4 := abs_nonneg t
  nlinarith

theorem solution :
    ∃ u : ℕ → ℝ → ℝ → ℝ,
      (∀ k, ContDiff ℝ 2 (fun p : ℝ × ℝ => u k p.1 p.2)) ∧
      (∀ k x y, deriv (fun x' => deriv (fun x'' => u k x'' y) x') x +
          deriv (fun y' => deriv (fun y'' => u k x y'') y') y = 0) ∧
      (∀ ε > 0, ∃ K, ∀ k ≥ K, ∀ x,
          |u k x 0| ≤ ε ∧ |deriv (fun y => u k x y) 0| ≤ ε) ∧
      (∀ y ≠ 0, ∀ M : ℝ, ∃ K, ∀ k ≥ K, ∃ x, M < |u k x y|) := by
  refine ⟨fun k x y => Real.cos ((k : ℝ) * x) * Real.cosh ((k : ℝ) * y) / (k : ℝ), ?_, ?_, ?_, ?_⟩
  · intro k
    fun_prop
  · intro k x y
    dsimp only
    rw [f3bf_dx1, f3bf_dx2, f3bf_dy1, f3bf_dy2]
    ring
  · intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    refine ⟨K, fun k hk x => ?_⟩
    dsimp only
    have hkK : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (lt_trans (by positivity) hK) hkK
    have h1 : 1 < (k : ℝ) * ε := by
      have := (div_lt_iff₀ hε).mp (lt_of_lt_of_le hK hkK)
      linarith
    constructor
    · rw [mul_zero, Real.cosh_zero, mul_one, abs_div, abs_of_pos hkpos, div_le_iff₀ hkpos]
      have := Real.abs_cos_le_one ((k : ℝ) * x)
      linarith
    · rw [f3bf_dy1]
      simp
      exact hε.le
  · intro y hy M
    obtain ⟨K, hK⟩ := exists_nat_gt (4 * |M| / y ^ 2 + 1)
    refine ⟨K, fun k hk => ⟨0, ?_⟩⟩
    dsimp only
    have hkK : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hy2 : 0 < y ^ 2 := by positivity
    have hq : 0 ≤ 4 * |M| / y ^ 2 := by positivity
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    rw [mul_zero, Real.cos_zero, one_mul]
    have hc := f3bf_cosh_ge ((k : ℝ) * y)
    have hcpos := Real.cosh_pos ((k : ℝ) * y)
    rw [abs_of_pos (div_pos hcpos hkpos), lt_div_iff₀ hkpos]
    have h1 : 4 * |M| < (k : ℝ) * y ^ 2 := by
      have := (div_lt_iff₀ hy2).mp (by linarith : 4 * |M| / y ^ 2 < (k : ℝ))
      linarith
    have h2 : (k : ℝ) * (4 * |M|) < (k : ℝ) * ((k : ℝ) * y ^ 2) := mul_lt_mul_of_pos_left h1 hkpos
    have h3 : M * (k : ℝ) ≤ |M| * (k : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self M) hkpos.le
    have e : ((k : ℝ) * y) ^ 2 = (k : ℝ) * ((k : ℝ) * y ^ 2) := by ring
    rw [e] at hc
    linarith
