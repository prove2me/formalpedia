-- Prove2me | solution 1 for cheb_pythag
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T10:28:33.956287+00:00
-- url     : https://prove2.me/submissions/36b703fc-a778-4020-b894-e46646ac2827

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Polynomial Polynomial.Chebyshev

namespace ChebPythag

/-- The evaluation of the Pythagorean polynomial at `cos θ` for `θ ∈ (0,π)` is zero. -/
lemma eval_cos_eq_zero (d : ℕ) (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi) :
    (1 - (Real.cos θ)^2) * ((derivative (T ℝ (d : ℤ))).eval (Real.cos θ))^2
      + (d : ℝ)^2 * ((T ℝ (d : ℤ)).eval (Real.cos θ))^2 = (d : ℝ)^2 := by
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ1 hθ2
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  -- T_d(cos θ) = cos(d θ)
  have hT : (T ℝ (d : ℤ)).eval (Real.cos θ) = Real.cos ((d : ℤ) * θ) := T_real_cos θ d
  -- T'_d(cos θ) = d * U_{d-1}(cos θ), and U_{d-1}(cos θ) sin θ = sin(d θ).
  have hU := U_real_cos θ ((d : ℤ) - 1)
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at hU
  -- hU : (U ℝ (d-1)).eval (cos θ) * sin θ = sin (↑d * θ)
  have hderiv : derivative (T ℝ (d : ℤ)) = ((d : ℤ) : ℝ[X]) * U ℝ ((d : ℤ) - 1) :=
    T_derivative_eq_U (d : ℤ)
  -- Evaluate the derivative.
  have hderiv_eval : (derivative (T ℝ (d : ℤ))).eval (Real.cos θ)
      = (d : ℝ) * (U ℝ ((d : ℤ) - 1)).eval (Real.cos θ) := by
    rw [hderiv, Polynomial.eval_mul]
    congr 1
    simp
  -- U eval: (U ℝ (d-1)).eval (cos θ) = sin(d θ) / sin θ
  have hUeval : (U ℝ ((d : ℤ) - 1)).eval (Real.cos θ) = Real.sin ((d : ℤ) * θ) / Real.sin θ := by
    rw [eq_div_iff hsin_ne]
    push_cast at hU ⊢
    linarith [hU]
  -- 1 - cos²θ = sin²θ
  have h1c : 1 - (Real.cos θ)^2 = (Real.sin θ)^2 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  -- Cast ((d : ℤ) : ℝ) = (d : ℝ)
  have hdc : (((d : ℤ) : ℝ)) = (d : ℝ) := by simp
  rw [h1c, hderiv_eval, hUeval, hT]
  -- Compute: sin²θ · (d · sin(dθ)/sinθ)² + d² cos²(dθ) = d² sin²(dθ) + d² cos²(dθ) = d²
  have hsq := Real.sin_sq_add_cos_sq ((d : ℤ) * θ)
  field_simp
  nlinarith [hsq, sq_nonneg (Real.sin θ), sq_nonneg (Real.sin ((d:ℤ)*θ)), sq_nonneg (Real.cos ((d:ℤ)*θ))]

end ChebPythag

open ChebPythag

theorem solution (d : ℕ) :
    ∀ c : ℝ, (1 - c^2) * ((Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c)^2 + (d : ℝ)^2 * ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval c)^2 = (d : ℝ)^2 := by
  intro c
  -- The Pythagorean polynomial vanishes identically.
  set P : Polynomial ℝ := (1 - X^2) * (derivative (T ℝ (d : ℤ)))^2
    + C ((d : ℝ)^2) * (T ℝ (d : ℤ))^2 - C ((d : ℝ)^2) with hP_def
  -- P.eval x = 0 for all x, because P has infinitely many roots.
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hIcc_inf : (Set.Ioo (-1 : ℝ) 1).Infinite := Set.infinite_coe_iff.mp (Set.Ioo.infinite (by norm_num))
    apply hIcc_inf.mono
    intro x hx
    -- x ∈ (-1, 1). Set θ := arccos x.
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot]
    have hx1 : -1 < x := hx.1
    have hx2 : x < 1 := hx.2
    have hx1' : -1 ≤ x := le_of_lt hx1
    have hx2' : x ≤ 1 := le_of_lt hx2
    set θ := Real.arccos x with hθ_def
    have hθpos : 0 < θ := Real.arccos_pos.mpr hx2
    have hθlt : θ < Real.pi := Real.arccos_lt_pi.mpr hx1
    have hcos : Real.cos θ = x := Real.cos_arccos hx1' hx2'
    have := eval_cos_eq_zero d θ hθpos hθlt
    rw [hcos] at this
    rw [hP_def]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]
    linarith
  -- Now use P = 0 to get the identity at c.
  have := congrArg (Polynomial.eval c) hP0
  rw [hP_def] at this
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_zero] at this
  linarith
