-- Prove2me | solution 1 for TauCeti.Real.tendsto_integral_inv_log_sq_mul_log_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:27:27.489541+00:00
-- url     : https://prove2.me/submissions/59de64bd-4d2c-404f-a117-c793edc06e4b

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The logarithmic integral

This file defines the offset logarithmic integral `Li x = ∫ t in 2..x, (log t)⁻¹` and proves the
prime-number-theorem normalisation `Li x ~ x / log x` as `x → ∞`.

The lower endpoint is `2` rather than `0`: the integrand has a nonintegrable singularity at
`t = 1`, so the unshifted `li` exists only as a principal value, while every arithmetic
application compares a prime count with `Li`. The endpoint agrees with the one used by the
partial-summation identities for prime counts, so the two can be combined without a shift of
origin.

The asymptotic is proved from the exact identity
`Li x = x / log x - 2 / log 2 + ∫ t in 2..x, ((log t) ^ 2)⁻¹`,
the fundamental theorem of calculus applied to `t ↦ t / log t`, together with the estimate that
the remaining integral is `o (x / log x)`. Splitting that integral at `√x` bounds it by
`√x / (log 2) ^ 2 + 4 * x / (log x) ^ 2`, and both terms are `o (x / log x)`.

## Main declarations

* `TauCeti.Real.logIntegral` — the offset logarithmic integral.
* `TauCeti.Real.le_logIntegral` — the elementary lower bound `(x - 2) / log x ≤ Li x`.
* `TauCeti.Real.logIntegral_eq_div_log_sub_add` — the antiderivative identity above.
* `TauCeti.Real.logIntegral_isEquivalent_div_log` — `Li x ~ x / log x` at infinity, with the
  quotient form `TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop`.
* `TauCeti.Real.tendsto_div_div_log_of_isLittleO_logIntegral` — an `o (x / log x)` error
  relative to `δ Li x` gives `f x / (x / log x) → δ`.
* `TauCeti.Real.isLittleO_integral_div_mul_log_sq` — for `f` interval integrable above `2` and of
  at most linear growth, `∫ t in 2..x, f t / (t * log t ^ 2)` is `o (x / log x)`.

The auxiliary bounds `TauCeti.Real.integral_inv_log_pow_le` and
`TauCeti.Real.le_integral_inv_log_pow` estimate `∫ t in a..b, ((log t) ^ n)⁻¹` by monotonicity of
the logarithm. They are stated for a general exponent because the identity above needs `n = 2`
while `Li` itself is the case `n = 1`.

## Roadmap role

This is the analytic half of Layer **6.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`,
which asks for `Li` together with `Li(x) ∼ x/log x` on the way to the transfer
`ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)` that Layer 10.3 exports as `primeCount_asymptotic_of_primeTheta`.
The weighted-remainder estimate `isLittleO_integral_div_mul_log_sq` is the analytic input to that
transfer: it is what absorbs the integral produced by Abel summation.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.

Mathlib's `Mathlib/NumberTheory/Chebyshev.lean` carries out this estimate for the rational
Chebyshev function, in `Chebyshev.integral_theta_div_log_sq_isLittleO`; the argument for a general
integrand below follows the same split into a bounded initial segment and a linearly bounded tail.
-/

 section

namespace TauCeti.Real
end TauCeti.Real
section TauCeti.Real
open TauCeti TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology

/-! ### Reciprocal powers of the logarithm -/

/-- Reciprocal powers of the logarithm are continuous to the right of its zero `t = 1`. -/
theorem TauCeti.Real.continuousOn_inv_log_pow (n : ℕ) :
    _root_.ContinuousOn (fun t : ℝ ↦ (_root_.Real.log t ^ n)⁻¹) (_root_.Set.Ioi 1) := by
  have hlog : _root_.ContinuousOn (fun t : ℝ ↦ _root_.Real.log t) (_root_.Set.Ioi 1) :=
    Real.continuousOn_log.mono fun t ht ↦ _root_.ne_of_gt (_root_.lt_trans _root_.one_pos ht)
  exact (hlog.pow n).inv₀ fun t ht ↦ _root_.ne_of_gt (_root_.pow_pos (_root_.Real.log_pos ht) n)

/-- Reciprocal powers of the logarithm are interval integrable on any interval to the right
of `1`. -/
theorem TauCeti.Real.intervalIntegrable_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    _root_.IntervalIntegrable (fun t : ℝ ↦ (_root_.Real.log t ^ n)⁻¹) _root_.MeasureTheory.MeasureSpace.volume a b := by
  refine ((_root_.TauCeti.Real.continuousOn_inv_log_pow n).mono fun t ht ↦ ?_).intervalIntegrable
  rw [_root_.Set.mem_uIcc] at ht
  rcases ht with ht | ht
  · exact _root_.lt_of_lt_of_le ha ht.1
  · exact _root_.lt_of_lt_of_le hb ht.1

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` above by the value of the
integrand at the left endpoint. -/
theorem TauCeti.Real.integral_inv_log_pow_le (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (_root_.Real.log t ^ n)⁻¹ ≤ (b - a) / _root_.Real.log a ^ n := by
  have hla : 0 < _root_.Real.log a := _root_.Real.log_pos ha
  have hb : 1 < b := _root_.lt_of_lt_of_le ha hab
  have hmono := _root_.intervalIntegral.integral_mono_on hab (_root_.TauCeti.Real.intervalIntegrable_inv_log_pow n ha hb)
    (g := fun _ ↦ (_root_.Real.log a ^ n)⁻¹) _root_.intervalIntegrable_const (fun t ht ↦ ?_)
  · simpa [_root_.smul_eq_mul, _root_.div_eq_mul_inv] using hmono
  · exact _root_.inv_anti₀ (_root_.pow_pos hla n)
      (_root_.pow_le_pow_left₀ hla.le (_root_.Real.log_le_log (by linarith) ht.1) n)



/-- The integrand `(log t ^ n)⁻¹` is nonnegative to the right of `1`, so its integral is. -/
theorem TauCeti.Real.integral_inv_log_pow_nonneg (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (_root_.Real.log t ^ n)⁻¹ := by
  refine _root_.intervalIntegral.integral_nonneg hab fun t ht ↦ ?_
  have : 0 < _root_.Real.log t := _root_.Real.log_pos (_root_.lt_of_lt_of_le ha ht.1)
  positivity

/-! ### The logarithmic integral -/











/-! ### The asymptotic `Li x ~ x / log x` -/





/-- Splitting at `√x` bounds the remainder integral of the antiderivative identity. -/
private theorem TauCeti.Real.integral_inv_log_sq_le {x : ℝ} (hx : 4 ≤ x) :
    (∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹) ≤ √x / _root_.Real.log 2 ^ 2 + 4 * x / _root_.Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : 2 ≤ √x := by
    have h4 : √(4 : ℝ) ≤ √x := _root_.Real.sqrt_le_sqrt hx
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, _root_.Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
  have hle : √x ≤ x := by
    rw [_root_.Real.sqrt_le_self_iff]
    exact _root_.Or.inr (by linarith)
  have hlogx : 0 < _root_.Real.log x := _root_.Real.log_pos (by linarith)
  have hlogsq : _root_.Real.log √x = _root_.Real.log x / 2 := _root_.Real.log_sqrt hx0.le
  have hsplit : (∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹) =
      (∫ t in (2 : ℝ)..√x, (_root_.Real.log t ^ 2)⁻¹) + ∫ t in √x..x, (_root_.Real.log t ^ 2)⁻¹ :=
    (_root_.intervalIntegral.integral_add_adjacent_intervals
      (_root_.TauCeti.Real.intervalIntegrable_inv_log_pow 2 _root_.one_lt_two (by linarith))
      (_root_.TauCeti.Real.intervalIntegrable_inv_log_pow 2 (by linarith) (by linarith))).symm
  have hb₁ : (∫ t in (2 : ℝ)..√x, (_root_.Real.log t ^ 2)⁻¹) ≤ √x / _root_.Real.log 2 ^ 2 := by
    refine _root_.le_trans (_root_.TauCeti.Real.integral_inv_log_pow_le 2 _root_.one_lt_two hsq) ?_
    have hpos : (0 : ℝ) < _root_.Real.log 2 ^ 2 := by positivity
    gcongr
    linarith
  have hb₂ : (∫ t in √x..x, (_root_.Real.log t ^ 2)⁻¹) ≤ 4 * x / _root_.Real.log x ^ 2 := by
    refine _root_.le_trans (_root_.TauCeti.Real.integral_inv_log_pow_le 2 (by linarith) hle) ?_
    rw [hlogsq, _root_.div_pow, _root_.div_div_eq_mul_div, _root_.div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [_root_.Real.sqrt_nonneg x]
  rw [hsplit]
  linarith

/-- The remainder integral of the antiderivative identity is `o (x / log x)`. -/
theorem solution :
    _root_.Filter.Tendsto (fun x : ℝ ↦ (∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹) * _root_.Real.log x / x)
      _root_.Filter.atTop (𝓝 0) := by
  have hsqrt : _root_.Filter.Tendsto (fun x : ℝ ↦ _root_.Real.log x / √x) _root_.Filter.atTop (𝓝 0) := by
    refine ((_root_.isLittleO_log_rpow_atTop (r := 1 / 2)
      (by norm_num)).tendsto_div_nhds_zero).congr' ?_
    filter_upwards [_root_.Filter.eventually_ge_atTop (0 : ℝ)] with x _
    rw [_root_.Real.sqrt_eq_rpow]
  refine _root_.squeeze_zero' (g := fun x : ℝ ↦ _root_.Real.log x / √x * (_root_.Real.log 2 ^ 2)⁻¹ + 4 / _root_.Real.log x)
    ?_ ?_ ?_
  · filter_upwards [_root_.Filter.eventually_ge_atTop (4 : ℝ)] with x hx
    have hlogx : 0 < _root_.Real.log x := _root_.Real.log_pos (by linarith)
    have hnn := _root_.TauCeti.Real.integral_inv_log_pow_nonneg 2 _root_.one_lt_two (by linarith : (2 : ℝ) ≤ x)
    positivity
  · filter_upwards [_root_.Filter.eventually_ge_atTop (4 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : 0 < _root_.Real.log x := _root_.Real.log_pos (by linarith)
    have hsqpos : (0 : ℝ) < √x := Real.sqrt_pos.mpr hx0
    have hsqx : √x * √x = x := _root_.Real.mul_self_sqrt hx0.le
    have hbound := _root_.TauCeti.Real.integral_inv_log_sq_le hx
    rw [_root_.div_le_iff₀ hx0]
    have hexp : (_root_.Real.log x / √x * (_root_.Real.log 2 ^ 2)⁻¹ + 4 / _root_.Real.log x) * x =
        (√x / _root_.Real.log 2 ^ 2 + 4 * x / _root_.Real.log x ^ 2) * _root_.Real.log x := by
      field_simp
      nlinarith [hsqx]
    rw [hexp]
    exact _root_.mul_le_mul_of_nonneg_right hbound hlogx.le
  · have h₁ : _root_.Filter.Tendsto (fun x : ℝ ↦ _root_.Real.log x / √x * (_root_.Real.log 2 ^ 2)⁻¹) _root_.Filter.atTop (𝓝 0) := by
      simpa using hsqrt.mul_const ((_root_.Real.log 2 ^ 2)⁻¹)
    have h₂ : _root_.Filter.Tendsto (fun x : ℝ ↦ (4 : ℝ) / _root_.Real.log x) _root_.Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop _root_.Real.tendsto_log_atTop
    simpa using h₁.add h₂





/-! ### A weighted remainder integral

The integral `∫ t in 2..x, f t / (t * log t ^ 2)` is what Abel summation leaves behind when a
logarithmically weighted counting function is converted into an unweighted one.  It is negligible
on the scale `x / log x` as soon as `f` grows at most linearly. -/















end TauCeti.Real

end
end
