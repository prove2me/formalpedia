-- Prove2me | solution 1 for TauCeti.LSeries.wienerIkehara
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:17:39.309856+00:00
-- url     : https://prove2.me/submissions/62666faf-1866-4282-875a-4731f073da5c

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Theorems.Thm_TauCeti_LSeries_LSeriesSummable_mul_fourier_of_nonneg
import Theorems.Thm_TauCeti_LSeries_tendsto_inv_mul_tsum_mul_div_atTop
import Theorems.Thm_TauCeti_LSeries_tendsto_tsum_term_mul_fourier_atTop
import Theorems.Thm_TauCeti_exists_contDiff_hasCompactSupport_fourier_nonneg
import Theorems.Thm_TauCeti_exists_sum_Icc_le_mul_of_isBigO
import Theorems.Thm_TauCeti_isBigO_sum_Icc_of_sum_Ioc_floor_mul_le

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Continuity of the Fourier transform of an integrable function

On a finite-dimensional real inner-product space, the Fourier transform `𝓕 F` of an integrable
`F` is continuous, and so is the inverse transform `𝓕⁻ F = 𝓕 F ∘ (-·)`. These are Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the inner-product pairing, packaged so
that consumers do not repeat the `innerₗ`/`continuous_inner` bridge at every call site.

Nothing here is specific to positive-definite functions or to the Bochner roadmap; the file sits
outside `TauCeti/Analysis/Bochner/` so that it can be used by any Fourier-analysis development.

## Main declarations

* `TauCeti.continuous_fourier_of_integrable`: `𝓕 F` is continuous for integrable `F`.
* `TauCeti.continuous_fourierInv_of_integrable`: `𝓕⁻ F` is continuous for integrable `F`.
-/

 section

open MeasureTheory
open scoped FourierTransform

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform of an integrable function is continuous. This is Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the inner-product pairing. -/
theorem continuous_fourier_of_integrable {F : V → ℂ} (hint : Integrable F) : Continuous (𝓕 F) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa only [innerₗ_apply_apply] using continuous_inner) hint



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
# Integrability of Fourier transforms of smooth compactly supported functions

A smooth compactly supported function is a Schwartz function, so its Fourier transform is also a
Schwartz function and hence integrable. This supplies the Fourier-integrability hypotheses needed
in dominated-convergence arguments, such as the Wiener--Ikehara boundary identity.

## Main declarations

* `TauCeti.integrable_fourier_of_contDiff_of_hasCompactSupport`: the Fourier transform of a
  smooth compactly supported function on a finite-dimensional real inner product space is
  integrable.
-/

 section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of a smooth compactly supported function is integrable. -/
theorem integrable_fourier_of_contDiff_of_hasCompactSupport (hf : ContDiff ℝ ∞ f)
    (hsupp : HasCompactSupport f) : Integrable (𝓕 f) := by
  have hcoe : ⇑(hsupp.toSchwartzMap hf) = f := by
    ext x
    simp
  have h : Integrable ((𝓕 (hsupp.toSchwartzMap hf) : SchwartzMap V E) : V → E) :=
    SchwartzMap.integrable _
  rwa [SchwartzMap.fourier_coe, hcoe] at h

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
# The smoothed asymptotic behind Wiener--Ikehara

`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff` writes the
difference between a Fourier-weighted Dirichlet series and its pole contribution as an integral
along the line `Re s = 1`, for every scale `x > 0`. That integral carries the oscillating factor
`x ^ (it)`, so the Riemann--Lebesgue lemma makes it vanish as `x → ∞`. This file records the
resulting asymptotic, and then evaluates the pole contribution in the limit.

The pole contribution is `A * ∫ u in Ici (-log x), 𝓕 psi (u / 2π)`. As `x → ∞` the cutoff
`-log x` runs off to `-∞`, so the integral fills up the whole line, where Fourier inversion
evaluates it as `2π * psi 0`. The Fourier-weighted series therefore has the honest limit
`2π * A * psi 0`; the constant `2π` is the Jacobian of the scaling `u ↦ u / 2π` fixed by the
`x ^ (it)` parameterization.

Only the pole-subtracted remainder `G` is assumed continuous on the closed half-plane `Re s ≥ 1`.
Nothing is assumed about `LSeries a` there, where it is a total function with junk values.

## Main results

* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_sub_pole_atTop`: the Fourier-weighted Dirichlet
  series and its pole contribution differ by `o(1)` as the scale `x` tends to infinity.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop`: the Fourier-weighted Dirichlet series
  itself tends to `2π * A * psi 0`.

Both are stated for an integrable, compactly supported test function, with the analytic
hypotheses that the two limit arguments actually consume: half-line integrability of `𝓕 psi` for
the first, and integrability of `𝓕 psi` together with continuity of `psi` at `0` for the Fourier
inversion in the second. The hypotheses that vary with the scale `x` are asked for only
eventually as `x → ∞`, which is all an `atTop` limit consumes. The suffixed `..._of_contDiff`
forms specialize both to a smooth test function, for which all of those are automatic.

## Provenance

The statement obtained by letting `x → ∞` in the boundary Fourier identity follows `limiting_cor`
in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0 `AxiomMath/PrimeNumberTheoremAnd`
repository, revision `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling
files `TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier` and
`TauCeti.NumberTheory.LSeries.WienerIkehara.Limit`. The evaluation of the limiting pole
contribution by Fourier inversion is not in that source, which keeps the truncated integral.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {G : ℂ → ℂ} {A : ℂ}







/-- The smoothed Wiener--Ikehara asymptotic for a smooth, compactly supported test function,
whose regularity supplies its integrability, the integrability of its Fourier transform and its
continuity at `0`. -/
theorem tendsto_tsum_term_mul_fourier_atTop_of_contDiff
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi)
    (hFsum : ∀ᶠ x : ℝ in atTop, LSeriesSummable
      (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) 1) :
    Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)))
      atTop (𝓝 (2 * (π : ℂ) * A * psi 0)) :=
  tendsto_tsum_term_mul_fourier_atTop hG hG' hsum
    (hpsi.continuous.integrable_of_hasCompactSupport hsupp) hsupp
    (integrable_fourier_of_contDiff_of_hasCompactSupport hpsi hsupp)
    hpsi.continuous.continuousAt hFsum

end TauCeti.LSeries

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

open Asymptotics Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff Topology

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ} {psi : ℝ → ℂ} {x : ℝ}

/-! ### The one-sided bound coming from the boundary data -/



/-! ### The partial-sum bound -/



/-! ### The Fourier weight -/



/-- **The smoothed Wiener--Ikehara asymptotic for nonnegative coefficients.** Testing the Dirichlet
series of a nonnegative coefficient system against a smooth compactly supported function on the
line `Re s = 1` gives the limit `2π A psi 0`, where `A` is the residue subtracted off by the
continuous boundary remainder `G`.

This is `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff` with its summability
hypothesis discharged: for nonnegative coefficients the boundary data itself forces the
Fourier-weighted series to converge at every large scale. The hypotheses are now exactly the
analytic input of Wiener--Ikehara. -/
theorem tendsto_tsum_term_mul_fourier_atTop_of_nonneg (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi) :
    Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)))
      atTop (𝓝 (2 * (π : ℂ) * A * psi 0)) :=
  tendsto_tsum_term_mul_fourier_atTop_of_contDiff hG hG' hsum hpsi hsupp <| by
    have hGseg : ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (Icc 1 2) :=
      hG.comp Complex.continuous_ofReal.continuousOn fun r hr ↦ by simpa using hr.1
    have hG'seg : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
        G (sigma : ℂ) = LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1) :=
      fun sigma h1 _ ↦ hG' sigma (by simpa using h1)
    have hsumseg : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → LSeriesSummable a (sigma : ℂ) :=
      fun sigma h1 _ ↦ hsum sigma h1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact LSeriesSummable_mul_fourier_of_nonneg ha hGseg hG'seg hsumseg hpsi hsupp hx

end TauCeti.LSeries

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
# The Chebyshev bound behind Wiener--Ikehara

For nonnegative coefficients `a` whose Dirichlet series has the Wiener--Ikehara boundary data
(summability on `Re s > 1` and a remainder `G = LSeries a - A / (s - 1)` continuous on
`Re s ≥ 1`), the partial sums grow at most linearly:
`∑_{1 ≤ n ≤ t} ‖a n‖ = O(t)`.

This is the Chebyshev-type bound that the Tauberian half of Wiener--Ikehara consumes to control
the tails of its test functions. It is derived from the boundary data and nonnegativity alone,
improving the crude `O(t log t)` bound `TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary`.

The argument has two steps.

* **A window bound.** Choose a smooth compactly supported test function `psi` whose Fourier
  transform is nonnegative, and at least some `c > 0` on a neighbourhood `|v| < η` of the origin
  (`TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg`). The smoothed asymptotic
  `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg` bounds the Fourier-weighted
  series `∑ a n / n * 𝓕 psi (log (n / x) / 2π)` for large `x`. All of its summands are
  nonnegative, and those with `q x < n ≤ x`, where `q = exp (-π η)`, carry a weight at least
  `c / x`. Hence `∑_{q x < n ≤ x} ‖a n‖ ≤ K x`.
* **Summing the windows.** A window bound with a fixed ratio `q < 1` implies linear growth of the
  partial sums, by peeling off the window `(q x, x]` and recursing on `q x`
  (`TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le`).

## Main results

* `TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`: **the Chebyshev bound**
  `∑_{1 ≤ n ≤ t} ‖a n‖ = O(t)` for nonnegative coefficients with Wiener--Ikehara boundary data.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

 section

open Asymptotics Complex Filter FourierTransform Real Set
open scoped ComplexOrder ContDiff Topology

namespace TauCeti.LSeries

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ}

/-- If `exp (-(π η)) x < n ≤ x`, the frequency `log (n / x) / 2π` lies within `η` of `0`. -/
private theorem dist_mul_log_div_lt {η x : ℝ} {n : ℕ} (hx : 0 < x)
    (hqn : Real.exp (-(π * η)) * x < n) (hnx : (n : ℝ) ≤ x) :
    dist (1 / (2 * π) * Real.log (n / x)) 0 < η := by
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hqn
  have hlog_le : Real.log (n / x) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one hx).2 hnx)
  have hlog_ge : -(π * η) < Real.log (n / x) := by
    rw [← Real.log_exp (-(π * η))]
    exact Real.log_lt_log (by positivity) (by rw [lt_div_iff₀ hx]; exact hqn)
  have hη : 0 < η := by nlinarith [Real.pi_pos]
  have hpi : (0 : ℝ) < 1 / (2 * π) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hpi.le hlog_le)]
  have h1 := mul_lt_mul_of_pos_left hlog_ge hpi
  have h2 : 1 / (2 * π) * -(π * η) = -(η / 2) := by
    field_simp
  linarith

/-- For nonnegative coefficients with Wiener--Ikehara boundary data, the Fourier-weighted series
tested against a smooth compactly supported function converges at every scale `x > 0`. -/
private theorem summable_term_mul_fourier_of_nonneg (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma) {psi : ℝ → ℂ}
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ ↦
      _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)) := by
  have hGseg : ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (Icc 1 2) :=
    hG.comp Complex.continuous_ofReal.continuousOn fun r hr ↦ by simpa using hr.1
  have h := LSeriesSummable_mul_fourier_of_nonneg ha hGseg
    (fun sigma h1 _ ↦ hG' sigma (by simpa using h1)) (fun sigma h1 _ ↦ hsum sigma h1)
    hpsi hsupp hx
  refine h.congr fun n ↦ ?_
  by_cases hn : n = 0
  · simp [_root_.LSeries.term, hn]
  · simp only [_root_.LSeries.term, hn, ite_false]
    ring

/-- The window bound: nonnegative coefficients with Wiener--Ikehara boundary data have
`∑_{q x < n ≤ x} ‖a n‖ ≤ K x` for all large `x`, for some ratio `0 < q < 1` and constant `K`. -/
private theorem exists_eventually_sum_Ioc_norm_le_of_boundary (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma) :
    ∃ q K : ℝ, 0 < q ∧ q < 1 ∧
      ∀ᶠ x : ℝ in atTop, ∑ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, ‖a n‖ ≤ K * x := by
  obtain ⟨psi, hpsi, hsupp, hnn, hpos⟩ :=
    TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg (V := ℝ)
  -- The Fourier transform of `psi` is at least `c > 0` on `|v| < η`.
  set c : ℝ := (𝓕 psi 0).re / 2 with hc
  have hc0 : 0 < c := half_pos (Complex.pos_iff.1 hpos).1
  have hcont : Continuous fun v : ℝ ↦ (𝓕 psi v).re :=
    Complex.continuous_re.comp (TauCeti.continuous_fourier_of_integrable
      (hpsi.continuous.integrable_of_hasCompactSupport hsupp))
  obtain ⟨η, hη, hηc⟩ := Metric.eventually_nhds_iff.1
    (hcont.continuousAt.eventually (lt_mem_nhds (by linarith : c < (𝓕 psi 0).re)))
  -- The smoothed series is eventually bounded by `M`.
  have hT := tendsto_tsum_term_mul_fourier_atTop_of_nonneg ha hG hG' hsum hpsi hsupp
  set M : ℝ := ‖2 * (π : ℂ) * A * psi 0‖ + 1 with hM
  have hbound := hT.norm.eventually (gt_mem_nhds (by linarith : ‖2 * (π : ℂ) * A * psi 0‖ < M))
  set q : ℝ := Real.exp (-(π * η))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
  refine ⟨q, M / c, hq0, hq1, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with x hxM hx
  set F : ℕ → ℂ := fun n ↦ 𝓕 psi (1 / (2 * π) * Real.log (n / x))
  set u : ℕ → ℂ := fun n ↦ _root_.LSeries.term a 1 n * F n
  have hunn : ∀ n, 0 ≤ u n := fun n ↦
    mul_nonneg (by simpa using _root_.LSeries.term_nonneg (ha n) 1) (hnn _)
  have husum : Summable u := summable_term_mul_fourier_of_nonneg ha hG hG' hsum hpsi hsupp hx
  have hre_sum : Summable fun n ↦ (u n).re := Complex.reCLM.summable husum
  -- Each summand in the window `(q x, x]` has real part at least `c / x * ‖a n‖`.
  have hwin : ∀ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, c / x * ‖a n‖ ≤ (u n).re := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.1 hn
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn2).trans (Nat.floor_le hx.le)
    have hqn : q * x < n := Nat.lt_of_floor_lt hn1
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < n := by positivity
    have hv := dist_mul_log_div_lt hx hqn hnx
    have hFn : c < (F n).re := hηc hv
    have hterm : _root_.LSeries.term a 1 n = ((‖a n‖ / n : ℝ) : ℂ) := by
      rw [_root_.LSeries.term_of_ne_zero hn0, cpow_one]
      conv_lhs => rw [Complex.eq_coe_norm_of_nonneg (ha n)]
      push_cast
      ring
    simp only [u, hterm, Complex.re_ofReal_mul]
    calc c / x * ‖a n‖ = ‖a n‖ / x * c := by ring
      _ ≤ ‖a n‖ / n * c := by gcongr
      _ ≤ ‖a n‖ / n * (F n).re := by gcongr
  have hsum_le : ∑ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, (u n).re ≤ M := by
    refine (hre_sum.sum_le_tsum _ fun n _ ↦ (Complex.nonneg_iff.1 (hunn n)).1).trans ?_
    rw [← Complex.re_tsum husum]
    exact (Complex.re_le_norm _).trans hxM.le
  have hmain : c / x * ∑ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, ‖a n‖ ≤ M := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum hwin).trans hsum_le
  rw [div_mul_eq_mul_div, div_le_iff₀ hx] at hmain
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  linarith

/-- **The Chebyshev bound.** Nonnegative coefficients whose Dirichlet series is summable on
`Re s > 1` and has a boundary remainder `G = LSeries a - A / (s - 1)` continuous on `Re s ≥ 1`
satisfy `∑_{1 ≤ n ≤ t} ‖a n‖ = O(t)`. -/
theorem isBigO_sum_Icc_norm_id_of_boundary (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma) :
    (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ‖a n‖) =O[atTop] fun t ↦ t := by
  obtain ⟨q, K, hq0, hq1, h⟩ := exists_eventually_sum_Ioc_norm_le_of_boundary ha hG hG' hsum
  exact isBigO_sum_Icc_of_sum_Ioc_floor_mul_le (fun n ↦ norm_nonneg (a n)) hq0.le hq1 h

end TauCeti.LSeries

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
# The Wiener--Ikehara theorem

Let `a n ≥ 0` have Dirichlet series `F s = ∑ a n n⁻ˢ` convergent on `Re s > 1`, and suppose that
`F s - κ / (s - 1)` agrees on `Re s > 1` with a function `G` continuous on `Re s ≥ 1`. The
Wiener--Ikehara theorem says that the partial sums then grow like `κ x`:
`x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`.

The analytic input is the smoothed asymptotic
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_schwartz_atTop`, which evaluates the limit of
`∑ a n / n * 𝓕 g (log (n / x) / 2π)` for a Schwartz function `g`. This file makes two passes.

* **Smooth cutoffs.** For a smooth function `Ψ` with compact support inside `(0, ∞)`, the weight
  `W v = e^{2πv} Ψ(e^{2πv})` is smooth and compactly supported, hence the Fourier transform of the
  Schwartz function `g = 𝓕⁻ W`, and `a n / n * W (log (n / x) / 2π) = x⁻¹ a n Ψ (n / x)`. Since
  `g 0 = ∫ W = (2π)⁻¹ ∫_{(0, ∞)} Ψ`, this gives `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ`.
* **The sharp cutoff.** The indicator of `(0, 1]` is squeezed between two bump functions. The lower
  bump is supported in `(0, 1)`; the upper bump equals `1` on `[ε, 1]`, and the coefficients with
  `n ≤ ε x` that it misses are controlled by the Chebyshev bound
  `TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`. Letting `ε → 0` gives the theorem.

The coefficients are real and nonnegative, the hypothesis on the series is `LSeriesHasSum` on the
open half-plane (Mathlib's `LSeries` is a total function, zero where the series diverges), and the
continuous extension is a separately named function `G`, so no junk value of `F` at `s = 1` or on
the line `Re s = 1` is ever used. The sign of `κ` is not assumed: it is forced by the conclusion.

## Main results

* `TauCeti.LSeries.tendsto_inv_mul_tsum_mul_div_atTop`: the smoothed asymptotic
  `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ` for a smooth `Ψ` with compact support in `(0, ∞)`.
* `TauCeti.LSeries.wienerIkehara`: **the Wiener--Ikehara theorem**,
  `x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ`.
* `TauCeti.LSeries.wienerIkehara_zero`: the case `κ = 0`, in which `F` itself extends continuously
  to `Re s ≥ 1` and the partial sums are `o(x)`.

## Provenance

The passage from Schwartz test functions to smooth cutoffs on `(0, ∞)` and then to the sharp
cutoff follows `WienerIkeharaSmooth`, `WienerIkeharaInterval` and `WienerIkeharaTheorem'` in
`PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0 `AxiomMath/PrimeNumberTheoremAnd`
repository, revision `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling
files in this directory. Here the smooth step is derived from the Schwartz-function asymptotic
by Fourier inversion on `𝓢(ℝ, ℂ)`, and the sharp step squeezes directly between two
`ContDiffBump`s, spending the Chebyshev bound only on the initial segment `n ≤ ε x`.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

 section

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff SchwartzMap Topology

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

/-! ### Smooth cutoffs on the positive half-line -/

section Smooth

variable {Ψ : ℝ → ℂ}











variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ}



end Smooth

/-! ### Bump functions on the positive half-line -/

section Bump

variable {c : ℝ} (φ : ContDiffBump c)

private lemma TauCeti.LSeries.tsupport_bump_subset (h : φ.rOut < c) : _root_.tsupport φ ⊆ _root_.Set.Ioi 0 := by
  rw [φ.tsupport_eq, _root_.Real.closedBall_eq_Icc]
  intro y hy
  exact _root_.lt_of_lt_of_le (by linarith) hy.1

private lemma TauCeti.LSeries.integral_Ioi_bump (h : φ.rOut < c) : ∫ y in _root_.Set.Ioi 0, φ y = ∫ y, φ y :=
  _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy ↦
    _root_.image_eq_zero_of_notMem_tsupport fun h' ↦ hy (_root_.TauCeti.LSeries.tsupport_bump_subset φ h h')

/-- A bump in `(0, ∞)` has integral at most the length `2 rOut` of its support. -/
private lemma TauCeti.LSeries.integral_Ioi_bump_le (h : φ.rOut < c) : ∫ y in _root_.Set.Ioi 0, φ y ≤ 2 * φ.rOut := by
  simpa [_root_.TauCeti.LSeries.integral_Ioi_bump φ h, φ.rOut_pos.le] using φ.integral_le_measure_closedBall (μ := _root_.MeasureTheory.MeasureSpace.volume)

/-- A bump in `(0, ∞)` has integral at least the length `2 rIn` of the ball where it is `1`. -/
private lemma TauCeti.LSeries.le_integral_Ioi_bump (h : φ.rOut < c) : 2 * φ.rIn ≤ ∫ y in _root_.Set.Ioi 0, φ y := by
  simpa [_root_.TauCeti.LSeries.integral_Ioi_bump φ h, φ.rIn_pos.le] using φ.measure_closedBall_le_integral (μ := _root_.MeasureTheory.MeasureSpace.volume)

end Bump

/-! ### The sharp cutoff -/

section Sharp

variable {a : ℕ → ℝ} {F G : ℂ → ℂ} {κ : ℝ}

/-- The smoothed asymptotic for real coefficients and a real bump in `(0, ∞)`. -/
private lemma TauCeti.LSeries.tendsto_inv_mul_tsum_mul_bump (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → _root_.LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : _root_.ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1))
    {c : ℝ} (φ : _root_.ContDiffBump c) (h : φ.rOut < c) :
    _root_.Filter.Tendsto (fun x : ℝ ↦ x⁻¹ * ∑' n : ℕ, a n * φ (n / x)) _root_.Filter.atTop
      (𝓝 (κ * ∫ y in _root_.Set.Ioi 0, φ y)) := by
  have hmain := _root_.TauCeti.LSeries.tendsto_inv_mul_tsum_mul_div_atTop (a := fun n ↦ (a n : ℂ)) (A := κ)
    (Ψ := fun y ↦ (φ y : ℂ)) (fun n ↦ by simpa using ha n) hG
    (fun z hz ↦ by rw [hGF z hz, (hF z hz).LSeries_eq])
    (fun σ hσ ↦ (hF σ (by simpa using hσ)).LSeriesSummable)
    (ofRealCLM.contDiff.comp φ.contDiff) (φ.hasCompactSupport.comp_left _root_.Complex.ofReal_zero)
    ((_root_.tsupport_comp_subset _root_.Complex.ofReal_zero φ).trans (_root_.TauCeti.LSeries.tsupport_bump_subset φ h))
  rw [_root_.integral_complex_ofReal, ← _root_.Complex.ofReal_mul] at hmain
  refine (continuous_re.tendsto _).comp hmain |>.congr fun x ↦ ?_
  simp only [_root_.Function.comp_apply, ← _root_.Complex.ofReal_inv, ← _root_.Complex.ofReal_mul, ← _root_.Complex.ofReal_tsum, _root_.Complex.ofReal_re]

/-- The lower bump lies below the sharp cutoff. -/
private lemma TauCeti.LSeries.tsum_mul_bump_le_sum (ha : 0 ≤ a) {c : ℝ} (φ : _root_.ContDiffBump c) (h : φ.rOut < c)
    (h1 : c + φ.rOut ≤ 1) {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, a n * φ (n / x) ≤ ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, a n := by
  have hzero : ∀ y : ℝ, y ∉ _root_.Set.Ioo 0 1 → φ y = 0 := fun y hy ↦ by
    by_contra h0
    have hy' : y ∈ _root_.Metric.ball c φ.rOut := φ.support_eq ▸ _root_.Function.mem_support.2 h0
    rw [_root_.Real.ball_eq_Ioo] at hy'
    exact hy ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  rw [_root_.tsum_eq_sum (s := _root_.Finset.Icc 1 ⌊x⌋₊) fun n hn ↦ ?_]
  · exact _root_.Finset.sum_le_sum fun n _ ↦ _root_.mul_le_of_le_one_right (ha n) φ.le_one
  refine _root_.mul_eq_zero_of_right _ (hzero _ fun hn' ↦ hn (_root_.Finset.mem_Icc.2 ⟨?_, ?_⟩))
  · by_contra h0
    simp_all
  · exact _root_.Nat.le_floor ((_root_.div_lt_one hx).1 hn'.2).le

/-- The upper bump, together with the initial segment `n ≤ ε x`, lies above the sharp cutoff. -/
private lemma TauCeti.LSeries.sum_Ioc_le_tsum_mul_bump (ha : 0 ≤ a) {c ε : ℝ} (φ : _root_.ContDiffBump c)
    (hε : c - φ.rIn ≤ ε) (h1 : 1 ≤ c + φ.rIn) (h2 : c + φ.rOut ≤ 2) {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ _root_.Finset.Ioc ⌊ε * x⌋₊ ⌊x⌋₊, a n ≤ ∑' n : ℕ, a n * φ (n / x) := by
  have hsum : _root_.Summable fun n : ℕ ↦ a n * φ (n / x) := by
    refine _root_.summable_of_ne_finset_zero (s := _root_.Finset.range (⌊2 * x⌋₊ + 1)) fun n hn ↦ ?_
    refine _root_.mul_eq_zero_of_right _ (φ.zero_of_le_dist ?_)
    have hn' : 2 * x < n := by
      simpa using _root_.Nat.lt_of_floor_lt (_root_.Nat.lt_of_lt_of_le (_root_.Nat.lt_succ_self _)
        (_root_.not_lt.1 (Finset.mem_range.not.1 hn)))
    rw [_root_.Real.dist_eq, _root_.le_abs]
    left
    have : 2 < (n : ℝ) / x := by rwa [_root_.lt_div_iff₀ hx]
    linarith
  refine _root_.le_trans (_root_.Finset.sum_le_sum fun n hn ↦ ?_)
    (hsum.sum_le_tsum _ fun n _ ↦ _root_.mul_nonneg (ha n) φ.nonneg)
  obtain ⟨hlo, hhi⟩ := _root_.Finset.mem_Ioc.1 hn
  have hlo' : ε * x < n := _root_.Nat.lt_of_floor_lt hlo
  have hhi' : (n : ℝ) ≤ x := (_root_.Nat.le_floor_iff hx.le).1 hhi
  rw [φ.one_of_mem_closedBall, _root_.mul_one]
  rw [_root_.Real.closedBall_eq_Icc]
  constructor
  · rw [_root_.le_div_iff₀ hx]
    nlinarith
  · rw [_root_.div_le_iff₀ hx]
    nlinarith

/-- **The squeeze at width `ε`.** Under a Chebyshev bound `∑_{1 ≤ n ≤ N} a n ≤ C N`, for every
`0 < ε ≤ 1 / 8` the normalized partial sums are eventually within `(C + 4 |κ| + 1) ε` of `κ`. -/
private lemma TauCeti.LSeries.eventually_abs_inv_mul_sum_sub_le (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → _root_.LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : _root_.ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, a n ≤ C * N) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∀ᶠ x in _root_.Filter.atTop, |x⁻¹ * ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, a n - κ| ≤ (C + 4 * |κ| + 1) * ε := by
  -- The upper bump is `1` on `[ε, 1]` and supported in `(ε / 2, 1 + ε / 2)`; the lower bump is
  -- supported in `(ε, 1 - ε)` and is `1` on `[2ε, 1 - 2ε]`.
  let φp : _root_.ContDiffBump ((1 + ε) / 2) := ⟨(1 - ε) / 2, 1 / 2, by linarith, by linarith⟩
  let φm : _root_.ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2 - 2 * ε, 1 / 2 - ε, by linarith, by linarith⟩
  have hp := _root_.TauCeti.LSeries.tendsto_inv_mul_tsum_mul_bump ha hF hG hGF φp (by simp [φp]; linarith)
  have hm := _root_.TauCeti.LSeries.tendsto_inv_mul_tsum_mul_bump ha hF hG hGF φm (by simp [φm]; linarith)
  -- Their integrals are within `ε` and `4ε` of `1`.
  have hIp := _root_.TauCeti.LSeries.integral_Ioi_bump_le φp (by simp [φp]; linarith)
  have hIp' := _root_.TauCeti.LSeries.le_integral_Ioi_bump φp (by simp [φp]; linarith)
  have hIm := _root_.TauCeti.LSeries.integral_Ioi_bump_le φm (by simp [φm]; linarith)
  have hIm' := _root_.TauCeti.LSeries.le_integral_Ioi_bump φm (by simp [φm]; linarith)
  simp only [φp, φm] at hIp hIp' hIm hIm'
  have hκp : |κ * (∫ y in _root_.Set.Ioi 0, φp y) - κ| ≤ |κ| * ε := by
    rw [← _root_.mul_sub_one, _root_.abs_mul]
    exact _root_.mul_le_mul_of_nonneg_left (_root_.abs_le.2 ⟨by linarith, by linarith⟩) (_root_.abs_nonneg κ)
  have hκm : |κ * (∫ y in _root_.Set.Ioi 0, φm y) - κ| ≤ |κ| * (4 * ε) := by
    rw [← _root_.mul_sub_one, _root_.abs_mul]
    exact _root_.mul_le_mul_of_nonneg_left (_root_.abs_le.2 ⟨by linarith, by linarith⟩) (_root_.abs_nonneg κ)
  filter_upwards [_root_.Filter.eventually_gt_atTop 0, _root_.Metric.tendsto_nhds.1 hp ε hε,
    _root_.Metric.tendsto_nhds.1 hm ε hε] with x hx0 hUx hLx
  rw [_root_.Real.dist_eq] at hUx hLx
  -- The lower squeeze.
  have hlow : x⁻¹ * ∑' n : ℕ, a n * φm (n / x) ≤ x⁻¹ * ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, a n :=
    _root_.mul_le_mul_of_nonneg_left (_root_.TauCeti.LSeries.tsum_mul_bump_le_sum ha φm (by simp [φm]; linarith)
      (by simp [φm]; linarith) hx0) (_root_.inv_nonneg.2 hx0.le)
  -- The upper squeeze: split off the initial segment `n ≤ ε x`, where the Chebyshev bound applies.
  have hsplit : ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, a n =
      ∑ n ∈ _root_.Finset.Icc 1 ⌊ε * x⌋₊, a n + ∑ n ∈ _root_.Finset.Ioc ⌊ε * x⌋₊ ⌊x⌋₊, a n := by
    have hI (m : ℕ) : _root_.Finset.Icc 1 m = _root_.Finset.Ioc 0 m := by
      simpa using _root_.Finset.Icc_add_one_left_eq_Ioc 0 m
    rw [hI, hI]
    exact (_root_.Finset.sum_Ioc_consecutive _ (_root_.Nat.zero_le _) (_root_.Nat.floor_mono (by nlinarith))).symm
  have hinit : ∑ n ∈ _root_.Finset.Icc 1 ⌊ε * x⌋₊, a n ≤ C * (ε * x) :=
    (hC _).trans (_root_.mul_le_mul_of_nonneg_left (_root_.Nat.floor_le (by positivity)) hC0)
  have hup : x⁻¹ * ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, a n ≤ C * ε + x⁻¹ * ∑' n : ℕ, a n * φp (n / x) := by
    have := _root_.TauCeti.LSeries.sum_Ioc_le_tsum_mul_bump ha φp (ε := ε) (by simp [φp]; linarith)
      (by simp [φp]; linarith) (by simp [φp]; linarith) hx0
    rw [hsplit, _root_.mul_add]
    refine _root_.add_le_add ?_ (_root_.mul_le_mul_of_nonneg_left this (_root_.inv_nonneg.2 hx0.le))
    rw [_root_.inv_mul_le_iff₀ hx0]
    linarith
  rw [_root_.abs_lt] at hUx hLx
  rw [_root_.abs_le] at hκp hκm ⊢
  constructor <;> nlinarith [_root_.abs_nonneg κ]

/-- **The Wiener--Ikehara theorem.** Let `a n ≥ 0` have Dirichlet series with sum `F s` on
`Re s > 1`, and let `G` be continuous on `Re s ≥ 1` with `G s = F s - κ / (s - 1)` on `Re s > 1`.
Then `x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`. -/
theorem solution (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → _root_.LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : _root_.ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1)) :
    _root_.Filter.Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, a n) _root_.Filter.atTop (𝓝 κ) := by
  -- The Chebyshev bound `∑_{1 ≤ n ≤ N} a n ≤ C N`.
  obtain ⟨C₀, hC₀⟩ := _root_.TauCeti.exists_sum_Icc_le_mul_of_isBigO
    (_root_.TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary (a := fun n ↦ (a n : ℂ)) (A := κ)
      (fun n ↦ by simpa using ha n) hG (fun z hz ↦ by rw [hGF z hz, (hF z hz).LSeries_eq])
      (fun σ hσ ↦ (hF σ (by simpa using hσ)).LSeriesSummable))
  set C := _root_.Max.max C₀ 0
  have hC0 : 0 ≤ C := _root_.le_max_right _ _
  have hC : ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, a n ≤ C * N := fun N ↦ by
    refine _root_.le_trans (_root_.le_of_eq (_root_.Finset.sum_congr _root_.rfl fun n _ ↦ ?_)) ((hC₀ N).trans
      (_root_.mul_le_mul_of_nonneg_right (_root_.le_max_left _ _) N.cast_nonneg))
    simp [_root_.abs_of_nonneg (ha n)]
  -- Squeeze at a width `ε` small enough that the error `(C + 4 |κ| + 1) ε` is below `δ`.
  rw [_root_.Metric.tendsto_atTop]
  intro δ hδ
  set K := C + 4 * |κ| + 2
  have hK : 0 < K := by positivity
  set ε := _root_.Min.min (1 / 8) (δ / K)
  have hε : 0 < ε := _root_.lt_min (by norm_num) (by positivity)
  have hεK : ε * K ≤ δ := by
    have := _root_.min_le_right (1 / 8) (δ / K)
    rwa [_root_.le_div_iff₀ hK] at this
  obtain ⟨x₀, hx₀⟩ := _root_.Filter.eventually_atTop.1
    (_root_.TauCeti.LSeries.eventually_abs_inv_mul_sum_sub_le ha hF hG hGF hC0 hC hε (_root_.min_le_left _ _))
  refine ⟨x₀, fun x hx ↦ (hx₀ x hx).trans_lt ?_⟩
  nlinarith



end Sharp

end TauCeti.LSeries

end
end
