-- Prove2me | solution 1 for TauCeti.Real.logIntegral_eq_div_log_sub_add
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:39:18.339602+00:00
-- url     : https://prove2.me/submissions/70d1a608-b759-4cfa-9c6a-5ee6b68e8ccf

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_LogIntegral
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_TauCeti_Real_hasDerivAt_div_log

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







/-! ### The logarithmic integral -/



/-- Defining equation of `TauCeti.Real.logIntegral`. -/
theorem TauCeti.Real.logIntegral_def (x : ℝ) : _root_.TauCeti.Real.logIntegral x = ∫ t in (2 : ℝ)..x, (_root_.Real.log t)⁻¹ := (_root_.rfl)







/-! ### The asymptotic `Li x ~ x / log x` -/



/-- **The antiderivative identity for the logarithmic integral.** Integrating the derivative of
`t ↦ t / log t` from `2` to `x` writes `Li x` as `x / log x` plus a constant and a remainder
integral, which the asymptotic below shows is `o (x / log x)`. -/
theorem solution {x : ℝ} (hx : 2 ≤ x) :
    _root_.TauCeti.Real.logIntegral x =
      x / _root_.Real.log x - 2 / _root_.Real.log 2 + ∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹ := by
  have hx1 : (1 : ℝ) < x := _root_.lt_of_lt_of_le _root_.one_lt_two hx
  have h1 : _root_.IntervalIntegrable (fun t : ℝ ↦ (_root_.Real.log t)⁻¹) _root_.MeasureTheory.MeasureSpace.volume 2 x := by
    simpa using _root_.TauCeti.Real.intervalIntegrable_inv_log_pow 1 _root_.one_lt_two hx1
  have h2 : _root_.IntervalIntegrable (fun t : ℝ ↦ (_root_.Real.log t ^ 2)⁻¹) _root_.MeasureTheory.MeasureSpace.volume 2 x :=
    _root_.TauCeti.Real.intervalIntegrable_inv_log_pow 2 _root_.one_lt_two hx1
  have hderiv : ∀ t ∈ _root_.Set.uIcc (2 : ℝ) x, _root_.HasDerivAt (fun u : ℝ ↦ u / _root_.Real.log u)
      ((_root_.Real.log t)⁻¹ - (_root_.Real.log t ^ 2)⁻¹) t := by
    intro t ht
    rw [_root_.Set.uIcc_of_le hx, _root_.Set.mem_Icc] at ht
    exact _root_.TauCeti.Real.hasDerivAt_div_log (by linarith [ht.1])
  have hFTC := _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (h1.sub h2)
  rw [_root_.intervalIntegral.integral_sub h1 h2] at hFTC
  rw [_root_.TauCeti.Real.logIntegral_def]
  linarith [hFTC]









/-! ### A weighted remainder integral

The integral `∫ t in 2..x, f t / (t * log t ^ 2)` is what Abel summation leaves behind when a
logarithmically weighted counting function is converted into an unweighted one.  It is negligible
on the scale `x / log x` as soon as `f` grows at most linearly. -/















end TauCeti.Real

end
end
