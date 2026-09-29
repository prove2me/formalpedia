-- Prove2me | solution 1 for bernstein_unit
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T13:08:40.128084+00:00
-- url     : https://prove2.me/submissions/253170f5-9d88-4177-a7b7-8c64c41b5b20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_cheb_compare_outer
import Theorems.Thm_cheb_deriv_abs_le
import Theorems.Thm_cos_shift_decompose
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

open Polynomial Polynomial.Chebyshev Real

theorem solution (Q : Polynomial ℝ) {d : ℕ} (hd : Q.natDegree ≤ d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |Q.eval x| ≤ 1) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → (1 - c^2) * (Q.derivative.eval c)^2 ≤ (d : ℝ)^2 := by
  intro c hc1 hc2
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: Q constant, Q' = 0.
    subst hd0
    have hQ0 : Q.natDegree = 0 := Nat.le_zero.mp hd
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hQ0
    rw [← ha, Polynomial.derivative_C, Polynomial.eval_zero]
    norm_num
  · -- d ≥ 1.
    have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
    have hdr_pos : (0 : ℝ) < (d : ℝ) := by linarith
    -- c = ±1: trivial.
    rcases eq_or_lt_of_le hc1 with hc1eq | hc1lt
    · have : (1 : ℝ) - c^2 = 0 := by rw [← hc1eq]; ring
      rw [this, zero_mul]; positivity
    rcases eq_or_lt_of_le hc2 with hc2eq | hc2lt
    · have : (1 : ℝ) - c^2 = 0 := by rw [hc2eq]; ring
      rw [this, zero_mul]; positivity
    -- c ∈ (-1, 1).
    set φ := Real.arccos c with hφ_def
    have hcos : Real.cos φ = c := Real.cos_arccos hc1 hc2
    have hsin : Real.sin φ = Real.sqrt (1 - c^2) := by
      rw [hφ_def]; exact Real.sin_arccos c
    have hsin_pos : (0 : ℝ) < Real.sin φ := by
      rw [hsin]; apply Real.sqrt_pos.mpr; nlinarith
    -- Obtain the odd-part polynomial P.
    obtain ⟨E, P, hEdeg, hPdeg, hident, hP1⟩ := cos_shift_decompose Q φ
    -- (1-x²) P(x)² ≤ 1 on [-1,1].
    have hPbound : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (P.eval x)^2 ≤ 1 := by
      intro x hx1 hx2
      set θ := Real.arccos x with hθ_def
      have hcosθ : Real.cos θ = x := Real.cos_arccos hx1 hx2
      have hsinθ : Real.sin θ = Real.sqrt (1 - x^2) := by
        rw [hθ_def]; exact Real.sin_arccos x
      have hsinθ_sq : (Real.sin θ)^2 = 1 - x^2 := by
        rw [hsinθ, Real.sq_sqrt (by nlinarith : (0:ℝ) ≤ 1 - x^2)]
      -- Q(cos(φ + θ)) = E(x) + P(x) sin θ and Q(cos(φ - θ)) = E(x) - P(x) sin θ.
      have h1 := hident θ
      have h2 := hident (-θ)
      rw [hcosθ] at h1
      rw [Real.cos_neg, Real.sin_neg, hcosθ, mul_neg] at h2
      -- Subtract: Q(cos(φ+θ)) - Q(cos(φ-θ)) = 2 P(x) sin θ.
      have hdiff : Q.eval (Real.cos (φ + θ)) - Q.eval (Real.cos (φ + -θ)) = 2 * P.eval x * Real.sin θ := by
        rw [h1, h2]; ring
      -- |Q(cos ·)| ≤ 1.
      have hQ1 : |Q.eval (Real.cos (φ + θ))| ≤ 1 := h _ (Real.neg_one_le_cos _) (Real.cos_le_one _)
      have hQ2 : |Q.eval (Real.cos (φ + -θ))| ≤ 1 := h _ (Real.neg_one_le_cos _) (Real.cos_le_one _)
      -- So |2 P(x) sin θ| ≤ 2.
      have : |2 * P.eval x * Real.sin θ| ≤ 2 := by
        rw [← hdiff]
        calc |Q.eval (Real.cos (φ + θ)) - Q.eval (Real.cos (φ + -θ))|
            ≤ |Q.eval (Real.cos (φ + θ))| + |Q.eval (Real.cos (φ + -θ))| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add hQ1 hQ2
          _ = 2 := by ring
      -- So (P(x) sin θ)² ≤ 1, i.e., (1-x²) P(x)² ≤ 1.
      have hsq : (P.eval x * Real.sin θ)^2 ≤ 1 := by nlinarith [this, abs_nonneg (2 * P.eval x * Real.sin θ), sq_abs (2 * P.eval x * Real.sin θ)]
      calc (1 - x^2) * (P.eval x)^2 = (P.eval x)^2 * (Real.sin θ)^2 := by rw [hsinθ_sq]; ring
        _ = (P.eval x * Real.sin θ)^2 := by ring
        _ ≤ 1 := hsq
    -- Set p := (C d) * P.
    set p : Polynomial ℝ := C (d : ℝ) * P with hp_def
    have hpdeg : p.natDegree < d := by
      rw [hp_def]
      have hPP : P.natDegree < d := by
        rcases hPdeg with h1 | h2
        · omega
        · rw [h2, Polynomial.natDegree_zero]; exact hdpos
      calc (C (d : ℝ) * P).natDegree ≤ P.natDegree := Polynomial.natDegree_C_mul_le _ _
        _ < d := hPP
    have hpbound : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2 := by
      intro x hx1 hx2
      rw [hp_def]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      have := hPbound x hx1 hx2
      nlinarith [this, sq_nonneg (P.eval x)]
    -- Apply cheb_compare_outer at c = 1.
    have hcmp := cheb_compare_outer p hdpos hpdeg hpbound 1 (by norm_num) (by norm_num) (by simp)
    have hT'1 := cheb_deriv_abs_le d 1 (by norm_num) (by norm_num)
    have hp1 : |p.eval 1| ≤ (d : ℝ)^2 := le_trans hcmp hT'1
    -- p(1) = d P(1) = d (-sin φ Q'(c)).
    have hp1val : p.eval 1 = (d : ℝ) * (-Real.sin φ * Q.derivative.eval c) := by
      rw [hp_def]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      rw [hP1, hcos]
    rw [hp1val] at hp1
    -- |d sin φ Q'(c)| ≤ d², so sin φ |Q'(c)| ≤ d.
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hsin_pos.le, abs_of_nonneg hdr_pos.le] at hp1
    have hsin2 : (Real.sin φ)^2 = 1 - c^2 := by
      rw [hsin, Real.sq_sqrt (by nlinarith : (0:ℝ) ≤ 1 - c^2)]
    -- (1-c²) Q'(c)² = sin²φ Q'(c)².
    have heq1 : (1 - c^2) * (Q.derivative.eval c)^2 = (Real.sin φ * |Q.derivative.eval c|)^2 := by
      rw [← hsin2, mul_pow, sq_abs]
    rw [heq1]
    have h1 : Real.sin φ * |Q.derivative.eval c| ≤ (d : ℝ) := by
      nlinarith [hp1, abs_nonneg (Q.derivative.eval c), hsin_pos, hdr_pos]
    nlinarith [h1, mul_nonneg hsin_pos.le (abs_nonneg (Q.derivative.eval c))]
