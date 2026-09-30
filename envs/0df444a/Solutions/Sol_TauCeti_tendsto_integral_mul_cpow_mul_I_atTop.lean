-- Prove2me | solution 1 for TauCeti.tendsto_integral_mul_cpow_mul_I_atTop
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:23:39.92968+00:00
-- url     : https://prove2.me/submissions/7850e644-da45-4bff-a60f-7455a64a0810

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Riemann--Lebesgue along a vertical line

Testing a function on the vertical line `Re s = c` against a Dirichlet series produces the
oscillating factor `x ^ (i t)`, which is the Fourier character of frequency `-(2π)⁻¹ log x` in
the variable `t`. Letting `x → ∞` therefore pushes the frequency out of every compact set, and the
Riemann--Lebesgue lemma makes the integral vanish.

## Main declarations

* `TauCeti.tendsto_integral_mul_cpow_mul_I_atTop`: the integral `∫ t, f t * x ^ (t * I)` tends to
  `0` as `x → ∞`, for an arbitrary `f : ℝ → ℂ`.
-/

 section

open Complex Filter MeasureTheory
open scoped FourierTransform Real Topology

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

/-- **Riemann--Lebesgue on a vertical line**: the integral of `f` against the oscillating factor
`x ^ (i t)` tends to `0` as `x → ∞`.

No hypothesis is needed on `f`. A limit along `atTop` only sees `x > 0`, and there the factor
`x ^ (i t)` has modulus `1`, so the integrand is integrable exactly when `f` is; when `f` is not
integrable both the left-hand side and the limit are `0`. (For `x ≤ 0` the equivalence fails —
at `x = 0` the integrand vanishes almost everywhere, and for `x < 0` the branch of the complex
power contributes a factor of modulus `exp (-π t)` — but those scales are irrelevant here.) -/
theorem solution (f : ℝ → ℂ) :
    _root_.Filter.Tendsto (fun x : ℝ ↦ ∫ t : ℝ, f t * (x : ℂ) ^ (t * _root_.Complex.I)) _root_.Filter.atTop (𝓝 0) := by
  have hfreq : _root_.Filter.Tendsto (fun x : ℝ ↦ -(_root_.Real.log x / (2 * π))) _root_.Filter.atTop (_root_.Filter.cocompact ℝ) :=
    (tendsto_neg_atTop_atBot.comp
      (Real.tendsto_log_atTop.atTop_div_const (by positivity))).mono_right _root_.atBot_le_cocompact
  refine _root_.Filter.Tendsto.congr' ?_ ((_root_.Real.tendsto_integral_exp_smul_cocompact f).comp hfreq)
  filter_upwards [_root_.Filter.eventually_gt_atTop 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [_root_.Function.comp_apply]
  refine _root_.MeasureTheory.integral_congr_ae (.of_forall fun t ↦ ?_)
  simp only [_root_.Circle.smul_def, _root_.smul_eq_mul, _root_.Real.fourierChar_apply]
  rw [_root_.Complex.cpow_def_of_ne_zero hx0, ← _root_.Complex.ofReal_log hx.le, _root_.mul_comm]
  congr 2
  push_cast
  field_simp

end TauCeti

end
end
