-- Prove2me | solution 1 for cheb_compare_outer
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T11:59:36.250501+00:00
-- url     : https://prove2.me/submissions/f06fdc22-68d3-4d1a-a8fb-8cbb7681a2a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_cheb_alt_compare
import Theorems.Thm_jordan_cos_sq_le
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

open Polynomial Polynomial.Chebyshev Real

theorem solution (p : Polynomial ℝ) {d : ℕ} (hd1 : 1 ≤ d) (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → (d : ℝ)^2 * (1 - c^2) ≤ 1 →
      |p.eval c| ≤ |(Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c| := by
  intro c hc1 hc2 hcase
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℕ) ≤ d := hd1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  -- d² > 0, so from d²(1-c²) ≤ 1, get 1-c² ≤ 1/d², i.e., c² ≥ 1-1/d².
  have hd2_pos : (0 : ℝ) < (d : ℝ)^2 := by positivity
  have hc2ge : (1 : ℝ) - 1/(d : ℝ)^2 ≤ c^2 := by
    have h1 : 1 - c^2 ≤ 1/(d:ℝ)^2 := by
      rw [le_div_iff₀ hd2_pos]
      nlinarith [hcase]
    linarith
  -- Jordan: cos(π/(2d))² ≤ 1 - 1/d² ≤ c².
  have hjordan := jordan_cos_sq_le d hd1
  have hcsq : Real.cos (Real.pi / (2 * d))^2 ≤ c^2 := le_trans hjordan hc2ge
  -- So cos(π/(2d)) ≤ |cos(π/(2d))| ≤ |c|.
  have hcabs : Real.cos (Real.pi / (2 * d)) ≤ |c| := by
    calc Real.cos (Real.pi / (2 * d)) ≤ |Real.cos (Real.pi / (2 * d))| := le_abs_self _
      _ ≤ |c| := by
          have h1 := Real.sqrt_le_sqrt hcsq
          rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h1
  exact cheb_alt_compare p hd1 hd h c hc1 hc2 hcabs
