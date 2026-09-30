-- Prove2me | solution 1 for TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:48:51.665586+00:00
-- url     : https://prove2.me/submissions/e864feeb-2e1c-4cb7-936d-fb999edb0fd9

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_LogIntegral
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_TauCeti_Real_logIntegral_eq_div_log_sub_add
import Theorems.Thm_TauCeti_Real_tendsto_integral_inv_log_sq_mul_log_div_atTop

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











/-! ### The logarithmic integral -/











/-! ### The asymptotic `Li x ~ x / log x` -/









/-- **The logarithmic integral is asymptotic to `x / log x`**, in quotient form. -/
theorem solution :
    _root_.Filter.Tendsto (fun x : ℝ ↦ _root_.TauCeti.Real.logIntegral x * _root_.Real.log x / x) _root_.Filter.atTop (𝓝 1) := by
  have hlog : _root_.Filter.Tendsto (fun x : ℝ ↦ _root_.Real.log x / x) _root_.Filter.atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hmain : _root_.Filter.Tendsto (fun x : ℝ ↦ 1 - 2 / _root_.Real.log 2 * (_root_.Real.log x / x) +
      (∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹) * _root_.Real.log x / x) _root_.Filter.atTop (𝓝 1) := by
    have hone : _root_.Filter.Tendsto (fun _ : ℝ ↦ (1 : ℝ)) _root_.Filter.atTop (𝓝 1) := _root_.tendsto_const_nhds
    have h := (hone.sub (hlog.const_mul (2 / _root_.Real.log 2))).add
      _root_.TauCeti.Real.tendsto_integral_inv_log_sq_mul_log_div_atTop
    simpa using h
  refine hmain.congr' ?_
  filter_upwards [_root_.Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < _root_.Real.log x := _root_.Real.log_pos (by linarith)
  rw [_root_.TauCeti.Real.logIntegral_eq_div_log_sub_add hx]
  field_simp



/-! ### A weighted remainder integral

The integral `∫ t in 2..x, f t / (t * log t ^ 2)` is what Abel summation leaves behind when a
logarithmically weighted counting function is converted into an unweighted one.  It is negligible
on the scale `x / log x` as soon as `f` grows at most linearly. -/















end TauCeti.Real

end
end
