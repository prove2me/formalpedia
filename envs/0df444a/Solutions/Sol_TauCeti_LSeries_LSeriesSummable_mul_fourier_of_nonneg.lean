-- Prove2me | solution 1 for TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:54:56.57381+00:00
-- url     : https://prove2.me/submissions/ac242e1a-0987-4fdd-b287-eff93d35c3a0

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Deriv
import Theorems.Thm_TauCeti_LSeries_LSeriesSummable_mul_of_norm_le
import Theorems.Thm_TauCeti_LSeries_isBigO_sum_Icc_norm_of_boundary

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Decay of Fourier transforms of smooth compactly supported functions

A smooth compactly supported function is a Schwartz function, so its Fourier transform is again a
Schwartz function and therefore decays faster than every negative power of `‖v‖`. This file records
that decay in the elementary form `‖v‖ ^ k * ‖𝓕 f v‖ ≤ C`, which is the shape a Fourier transform
is used in when it weights a comparison test.

## Main declarations

* `TauCeti.exists_norm_pow_mul_norm_fourier_le`: for every exponent `k`, the Fourier transform of a
  smooth compactly supported function on a finite-dimensional real inner product space satisfies
  `‖v‖ ^ k * ‖𝓕 f v‖ ≤ C` for some `C > 0`.
-/

 section

open scoped ContDiff FourierTransform

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of a smooth compactly supported function decays faster than every power
of `‖v‖⁻¹`, because it is a Schwartz function. -/
theorem exists_norm_pow_mul_norm_fourier_le (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f)
    (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ v : V, ‖v‖ ^ k * ‖𝓕 f v‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := (𝓕 (hsupp.toSchwartzMap hf) : SchwartzMap V E).decay k 0
  refine ⟨C, hC0, fun v ↦ ?_⟩
  have hcoe0 : ⇑(hsupp.toSchwartzMap hf) = f := by
    ext u
    simp
  have h := hC v
  rwa [norm_iteratedFDeriv_zero, SchwartzMap.fourier_coe, hcoe0] at h

end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A growth bound for nonnegative coefficients, and the summability it supplies

The smoothed Wiener--Ikehara asymptotic
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop` still carries a summability hypothesis: the
Fourier-weighted series `∑ a n 𝓕 psi (log (n / x) / 2π) / n` has to converge on the boundary line
`Re s = 1`, where the coefficients are no longer damped by `n ^ (-(sigma - 1))`. This file removes
that hypothesis for nonnegative coefficients, which is the only case Wiener--Ikehara is about.

The input is coefficient nonnegativity together with the boundary remainder data on the real
segment `sigma ∈ (1, 2]`; the growth bound for the partial sums is derived from them, not assumed.
Nonnegativity turns the boundary data into the one-sided estimate
`∑ ‖a n‖ / n ^ sigma ≤ B / (sigma - 1)` on `(1, 2]`, and inserting
`sigma = 1 + 1 / log t` into it bounds `∑_{n ≤ t} ‖a n‖` by a multiple of `t log t`. That is weaker
than the Chebyshev bound `O(t)` which Wiener--Ikehara ultimately proves, but it is available before
any Tauberian argument, and one logarithm to spare is all the summability needs: the Fourier
transform of a smooth compactly supported function decays faster than `|v| ^ (-3)`, so the factor
attached to `a n` is `O((log n) ^ (-3))`, and the Abel-summation bound
`TauCeti.LSeries.LSeriesSummable_mul_of_norm_le` converts `O(t log t)` partial sums into a
convergent series.

Only the values of the boundary remainder on the real segment `sigma ∈ (1, 2]` enter the growth
bound, so the results below are stated with the boundary data restricted to that segment; the final
asymptotic specializes the half-plane hypotheses it inherits from
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff`.

## Main results

* `TauCeti.LSeries.tsum_norm_term_le_of_boundary`: nonnegative coefficients with a boundary
  remainder continuous on the segment `[1, 2]` have a convergent norm series with
  `∑ ‖term a sigma n‖ ≤ B / (sigma - 1)` on `(1, 2]`.
* `TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary`: the resulting `O(t log t)` bound for the
  partial sums.
* `TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg`: the Fourier weight is small enough for
  that bound to force summability at `s = 1`, at every scale `x > 0`.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg`: **the smoothed Wiener--Ikehara
  asymptotic for nonnegative coefficients**, with no summability hypothesis left.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Asymptotics Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff Topology

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ} {psi : ℝ → ℂ} {x : ℝ}

/-! ### The one-sided bound coming from the boundary data -/



/-! ### The partial-sum bound -/



/-! ### The Fourier weight -/

/-- **The Fourier-weighted series converges on the boundary line.** For nonnegative coefficients
with a boundary remainder continuous on the segment `[1, 2]` and a smooth compactly supported test
function, the series tested at scale `x > 0` is summable at `s = 1`. This discharges the standing
summability hypothesis of
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff`. -/
theorem solution (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (_root_.Set.Icc 1 2))
    (hG' : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      G (sigma : ℂ) = _root_.LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → _root_.LSeriesSummable a (sigma : ℂ))
    (hpsi : _root_.ContDiff ℝ ∞ psi) (hsupp : _root_.HasCompactSupport psi) (hx : 0 < x) :
    _root_.LSeriesSummable (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) 1 := by
  obtain ⟨C, hC0, hC⟩ := _root_.TauCeti.exists_norm_pow_mul_norm_fourier_le hpsi hsupp 3
  have hpi : (0 : ℝ) < π := _root_.Real.pi_pos
  refine _root_.TauCeti.LSeries.LSeriesSummable_mul_of_norm_le (D := 8 * C * (4 * π) ^ 3)
    (_root_.TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary ha hG hG' hsum) ?_
  filter_upwards [_root_.Filter.eventually_ge_atTop (_root_.Max.max ⌈_root_.Real.exp 1⌉₊ ⌈x ^ 2⌉₊)] with n hn
  have hn1 : ⌈_root_.Real.exp 1⌉₊ ≤ n := _root_.le_trans (_root_.le_max_left _ _) hn
  have hn2 : ⌈x ^ 2⌉₊ ≤ n := _root_.le_trans (_root_.le_max_right _ _) hn
  have hne : _root_.Real.exp 1 ≤ (n : ℝ) := _root_.le_trans (_root_.Nat.le_ceil _) (_root_.Nat.cast_le.2 hn1)
  have hn0 : (0 : ℝ) < (n : ℝ) := _root_.lt_of_lt_of_le (_root_.Real.exp_pos 1) hne
  have hL1 : (1 : ℝ) ≤ _root_.Real.log n := (_root_.Real.le_log_iff_exp_le hn0).2 hne
  have hx2 : x ^ 2 ≤ (n : ℝ) := _root_.le_trans (_root_.Nat.le_ceil _) (_root_.Nat.cast_le.2 hn2)
  have hlogx : 2 * _root_.Real.log x ≤ _root_.Real.log n := by
    have h := _root_.Real.log_le_log (by positivity) hx2
    rwa [_root_.Real.log_pow] at h
  have hv : 1 / (2 * π) * _root_.Real.log ((n : ℝ) / x) = (_root_.Real.log n - _root_.Real.log x) / (2 * π) := by
    rw [_root_.Real.log_div hn0.ne' hx.ne']
    ring
  have hvge : _root_.Real.log n / (4 * π) ≤ 1 / (2 * π) * _root_.Real.log ((n : ℝ) / x) := by
    rw [hv, _root_.div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hvnn : (0 : ℝ) ≤ 1 / (2 * π) * _root_.Real.log ((n : ℝ) / x) :=
    _root_.le_trans (by positivity) hvge
  have hcube : (_root_.Real.log n / (4 * π)) ^ 3 * ‖𝓕 psi (1 / (2 * π) * _root_.Real.log ((n : ℝ) / x))‖ ≤ C := by
    refine _root_.le_trans (_root_.mul_le_mul_of_nonneg_right ?_ (_root_.norm_nonneg _)) (hC _)
    rw [_root_.Real.norm_of_nonneg hvnn]
    exact _root_.pow_le_pow_left₀ (by positivity) hvge 3
  have hfrac : (_root_.Real.log n / (4 * π)) ^ 3 = _root_.Real.log n ^ 3 / (64 * π ^ 3) := by
    field_simp
    ring
  rw [hfrac, _root_.div_mul_eq_mul_div, _root_.div_le_iff₀ (by positivity)] at hcube
  rw [_root_.le_div_iff₀ (by positivity : (0 : ℝ) < (1 + Real.log n) ^ 3)]
  have hpow : (1 + _root_.Real.log n) ^ 3 ≤ 8 * _root_.Real.log n ^ 3 := by nlinarith [_root_.sq_nonneg (_root_.Real.log n - 1)]
  nlinarith [_root_.norm_nonneg (𝓕 psi (1 / (2 * π) * _root_.Real.log ((n : ℝ) / x))),
    _root_.mul_le_mul_of_nonneg_left hpow
      (_root_.norm_nonneg (𝓕 psi (1 / (2 * π) * _root_.Real.log ((n : ℝ) / x))))]



end TauCeti.LSeries

end
end
