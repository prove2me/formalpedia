-- Prove2me | solution 1 for cheb_zeros_props
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T12:41:25.160641+00:00
-- url     : https://prove2.me/submissions/c4a8e483-d818-4e7b-8a11-bc4a1c1dcf05

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Polynomial Polynomial.Chebyshev Real

namespace ChebZerosProps

/-- `cos((2j+1)π/2) = 0` : argument is an odd multiple of `π/2`. -/
lemma cos_odd_pi_div_two (j : ℕ) : Real.cos ((2 * (j : ℝ) + 1) * Real.pi / 2) = 0 := by
  have h : (2 * (j : ℝ) + 1) * Real.pi / 2 = (j : ℝ) * Real.pi + Real.pi / 2 := by ring
  have hsin : Real.sin ((j : ℝ) * Real.pi) = 0 := by
    rw [show ((j : ℝ) * Real.pi) = (j : ℤ) * Real.pi by push_cast; ring]
    exact Real.sin_int_mul_pi j
  rw [h, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hsin]
  ring

/-- `sin((2j+1)π/2) = (-1)^j`. -/
lemma sin_odd_pi_div_two (j : ℕ) : Real.sin ((2 * (j : ℝ) + 1) * Real.pi / 2) = (-1 : ℝ)^j := by
  have h : (2 * (j : ℝ) + 1) * Real.pi / 2 = (j : ℝ) * Real.pi + Real.pi / 2 := by ring
  have hcos : Real.cos ((j : ℝ) * Real.pi) = (-1 : ℝ)^j := by
    rw [show ((j : ℝ) * Real.pi) = (j : ℤ) * Real.pi by push_cast; ring]
    rw [Real.cos_int_mul_pi j]
    norm_cast
  rw [h, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hcos]
  ring

end ChebZerosProps

open ChebZerosProps

theorem solution (d : ℕ) (hd : 1 ≤ d) (j : ℕ) (hj : j < d) :
    let θj := (2 * (j : ℝ) + 1) * Real.pi / (2 * d);
    (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (Real.cos θj) = 0 ∧
    0 < (-1:ℝ)^j * (Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval (Real.cos θj) ∧
    -1 < Real.cos θj ∧ Real.cos θj < 1 := by
  have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hjr : (j : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hj
  have hpi := Real.pi_pos
  set θj : ℝ := (2 * (j : ℝ) + 1) * Real.pi / (2 * d) with hθ_def
  -- θj ∈ (0, π).
  have hθj_pos : (0 : ℝ) < θj := by rw [hθ_def]; positivity
  have hθj_lt_pi : θj < Real.pi := by
    rw [hθ_def, div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hsinθ_pos : (0 : ℝ) < Real.sin θj := Real.sin_pos_of_pos_of_lt_pi hθj_pos hθj_lt_pi
  -- d · θj = (2j+1)π/2.
  have hdθ : (d : ℝ) * θj = (2 * (j : ℝ) + 1) * Real.pi / 2 := by
    rw [hθ_def]; field_simp
  -- Part 1: T_d(cos θj) = cos(d θj) = 0.
  have hT0 : (T ℝ (d : ℤ)).eval (Real.cos θj) = 0 := by
    rw [T_real_cos θj (d : ℤ)]
    have : ((d : ℤ) : ℝ) * θj = (2 * (j : ℝ) + 1) * Real.pi / 2 := by push_cast; linarith [hdθ]
    rw [this, cos_odd_pi_div_two]
  -- Part 2: U_{d-1}(cos θj) sin θj = sin(d θj) = (-1)^j.
  have hUsin := U_real_cos θj ((d : ℤ) - 1)
  have hsub : (((d : ℤ) - 1 : ℤ) : ℝ) + 1 = ((d : ℤ) : ℝ) := by push_cast; ring
  rw [hsub] at hUsin
  have hUsin' : (U ℝ ((d : ℤ) - 1)).eval (Real.cos θj) * Real.sin θj = (-1 : ℝ)^j := by
    rw [hUsin]
    have : ((d : ℤ) : ℝ) * θj = (2 * (j : ℝ) + 1) * Real.pi / 2 := by push_cast; linarith [hdθ]
    rw [this, sin_odd_pi_div_two]
  -- T'_d = d U_{d-1}, so T'_d(cos θj) = d U_{d-1}(cos θj) = d(-1)^j / sin θj.
  have hderiv : derivative (T ℝ (d : ℤ)) = ((d : ℤ) : ℝ[X]) * U ℝ ((d : ℤ) - 1) :=
    T_derivative_eq_U (d : ℤ)
  have hT'eval : (derivative (T ℝ (d : ℤ))).eval (Real.cos θj)
      = (d : ℝ) * ((U ℝ ((d : ℤ) - 1)).eval (Real.cos θj)) := by
    rw [hderiv]; simp [Polynomial.eval_mul]
  have halt : (0 : ℝ) < (-1:ℝ)^j * (derivative (T ℝ (d : ℤ))).eval (Real.cos θj) := by
    rw [hT'eval]
    have hU_val : (U ℝ ((d : ℤ) - 1)).eval (Real.cos θj) = (-1:ℝ)^j / Real.sin θj := by
      rw [eq_div_iff (ne_of_gt hsinθ_pos)]; exact hUsin'
    rw [hU_val]
    have hj2 : ((-1:ℝ)^j)^2 = 1 := by
      rw [← pow_mul, pow_mul']
      simp
    have : (-1:ℝ)^j * ((d : ℝ) * ((-1:ℝ)^j / Real.sin θj)) = (d : ℝ) / Real.sin θj := by
      field_simp
      nlinarith [hj2]
    rw [this]
    positivity
  -- Part 3: cos θj ∈ (-1, 1).
  have hcos_lt : Real.cos θj < 1 := by
    calc Real.cos θj < Real.cos 0 := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθj_lt_pi.le hθj_pos
      _ = 1 := Real.cos_zero
  have hcos_gt : -1 < Real.cos θj := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hθj_pos.le le_rfl hθj_lt_pi
    rw [Real.cos_pi] at this
    linarith
  exact ⟨hT0, halt, hcos_gt, hcos_lt⟩
