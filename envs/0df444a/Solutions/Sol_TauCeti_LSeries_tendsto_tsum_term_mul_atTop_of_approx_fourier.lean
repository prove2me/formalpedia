-- Prove2me | solution 1 for TauCeti.LSeries.tendsto_tsum_term_mul_atTop_of_approx_fourier
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:02:57.872602+00:00
-- url     : https://prove2.me/submissions/845be9b0-24ac-4530-8c8e-dad87cdcce19

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_LSeries_WienerIkehara_Approximation
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
import Theorems.Thm_TauCeti_LSeries_tendsto_tsum_term_mul_fourier_atTop
import Theorems.Thm_TauCeti_exists_contDiff_hasCompactSupport_fourier_nonneg
import Theorems.Thm_TauCeti_exists_sum_Icc_le_mul_of_isBigO
import Theorems.Thm_TauCeti_isBigO_sum_Icc_of_sum_Ioc_floor_mul_le
import Theorems.Thm_TauCeti_sum_range_mul_le_sum_range_mul

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
# Approximating the test function in the smoothed Wiener--Ikehara asymptotic

`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg` evaluates the limit of
`∑ a n / n * 𝓕 psi (log (n / x) / 2π)` for a *smooth compactly supported* test function `psi`.
The Tauberian step of Wiener--Ikehara needs the same limit for weights `W` that are not of this
form. A nonzero smooth compactly supported weight `W` is one: it is the Fourier transform of a
Schwartz function, but never of a compactly supported one, since a nonzero function and its
Fourier transform cannot both have compact support. This file passes the limit from `𝓕 psi` to
any weight `W` that such transforms approximate in the weighted sup norm
`sup_v (1 + v ^ 2) ‖W v - 𝓕 psi v‖`.

The approximation step rests on a uniform bound. If the partial sums of `‖a‖` satisfy the
Chebyshev bound `∑_{1 ≤ n ≤ N} ‖a n‖ ≤ C N`, then
`∑ ‖a n‖ / n * (1 + (log (n / x) / 2π) ^ 2)⁻¹ ≤ C (1 + 2π²)` for every scale `x > 0`.
The weight `t ↦ (t (1 + (log (t / x) / 2π) ^ 2))⁻¹` is antitone on `t > 0`, so Abel's inequality
`TauCeti.sum_range_mul_le_sum_range_mul` bounds the weighted sum by `C` times the sum of the
weight, and the integral test bounds the latter by `1 + ∫ = 1 + 2π (arctan - arctan) ≤ 1 + 2π²`.
Consequently a weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹` gives a series of size at most
`M C (1 + 2π²)`, uniformly in `x`, and a small error in the weighted sup norm costs little in the
limit. For nonnegative coefficients with Wiener--Ikehara boundary data the Chebyshev bound is
`TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`.

## Main results

* `TauCeti.LSeries.tsum_norm_term_mul_inv_one_add_sq_le`: the uniform bound on the
  logarithmically weighted series, from a Chebyshev bound.
* `TauCeti.LSeries.LSeriesSummable_mul_comp_log_div` and
  `TauCeti.LSeries.norm_tsum_term_mul_comp_log_div_le`: summability and the uniform bound for a
  weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹`.
* `TauCeti.LSeries.tendsto_tsum_term_mul_atTop_of_approx_fourier`: the smoothed Wiener--Ikehara
  asymptotic for a weight `W` approximable by Fourier transforms of smooth compactly supported
  functions `psi` whose values `psi 0` approximate `L`; the limit is `2π A L`.

## Provenance

The uniform bound and the truncation argument follow `bound_sum_log`, `bound_I1` and
`limiting_cor_W21` in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling files in this
directory. Here the summation by parts is the general `TauCeti.sum_range_mul_le_sum_range_mul`,
the integral of the weight is bounded on finite intervals by the fundamental theorem of calculus
rather than evaluated on `(0, ∞)`, and the approximation hypothesis is stated for an arbitrary
weight `W` instead of a fixed truncation of a `W^{2,1}` function. For a Schwartz function `g`
(`limiting_cor_schwartz` there) the approximants are the truncations `χ (R⁻¹ • ·) • g`, which
converge to `g` in the Schwartz topology (`SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`);
the weighted sup norm of a Fourier transform is bounded by two Schwartz seminorms, so it is the
continuity of the Fourier transform on `𝓢(ℝ, ℂ)` that makes the truncation error small.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Complex Filter FourierTransform Real Set
open scoped ComplexOrder ContDiff SchwartzMap Topology

variable {a : ℕ → ℂ} {C x : ℝ}

/-! ### The logarithmic weight -/



private lemma TauCeti.LSeries.one_div_two_pi_pos : (0 : ℝ) < 1 / (2 * π) := by positivity

private lemma TauCeti.LSeries.one_div_two_pi_le_one : 1 / (2 * π) ≤ 1 := by
  rw [_root_.div_le_one (by positivity)]
  linarith [_root_.Real.two_le_pi]

private lemma TauCeti.LSeries.hasDerivAt_log_div (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    _root_.HasDerivAt (fun t ↦ _root_.Real.log (t / x)) t⁻¹ t := by
  convert ((_root_.hasDerivAt_id' t).div_const x).log (_root_.div_pos ht hx).ne' using 1
  field_simp

/-- `t (1 + (log (t / x) / 2π) ^ 2)` has derivative `1 + b² L² + 2 b² L` at `t > 0`, where
`b = 1 / 2π` and `L = log (t / x)`. -/
private lemma TauCeti.LSeries.hasDerivAt_logWeight_denom (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    _root_.HasDerivAt (fun t ↦ t * (1 + (1 / (2 * π) * _root_.Real.log (t / x)) ^ 2))
      (1 + (1 / (2 * π) * _root_.Real.log (t / x)) ^ 2 +
        2 * (1 / (2 * π)) ^ 2 * _root_.Real.log (t / x)) t := by
  refine ((_root_.hasDerivAt_id' t).mul
    ((((_root_.TauCeti.LSeries.hasDerivAt_log_div hx ht).const_mul (1 / (2 * π))).pow 2).const_add 1)).congr_deriv ?_
  have := Real.pi_pos.ne'
  simp only [_root_.Pi.pow_apply, _root_.Nat.cast_ofNat]
  set L := _root_.Real.log (t / x)
  field_simp
  have h : π * L * π⁻¹ = L := by field_simp
  linear_combination 2 * h

private lemma TauCeti.LSeries.logWeight_denom_pos (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    0 < t * (1 + (1 / (2 * π) * _root_.Real.log (t / x)) ^ 2) := by
  have := hx
  positivity

/-- The logarithmic weight is antitone on `t > 0`: the derivative `1 + b² L² + 2 b² L` of its
reciprocal equals `b² (L + 1) ^ 2 + (1 - b²)`, which is nonnegative because `b = 1 / 2π ≤ 1`. -/
private lemma TauCeti.LSeries.antitoneOn_logWeight (hx : 0 < x) : _root_.AntitoneOn (_root_.TauCeti.LSeries.logWeight x) (_root_.Set.Ioi 0) := by
  have hmono : _root_.MonotoneOn (fun t ↦ t * (1 + (1 / (2 * π) * _root_.Real.log (t / x)) ^ 2)) (_root_.Set.Ioi 0) := by
    refine _root_.monotoneOn_of_hasDerivWithinAt_nonneg (_root_.convex_Ioi 0)
      (fun t ht ↦ (_root_.TauCeti.LSeries.hasDerivAt_logWeight_denom hx ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (_root_.TauCeti.LSeries.hasDerivAt_logWeight_denom hx
        (by simpa only [_root_.interior_Ioi, _root_.Set.mem_Ioi] using ht)).hasDerivWithinAt) fun t _ ↦ ?_
    have hb0 := _root_.TauCeti.LSeries.one_div_two_pi_pos
    have hb1 := _root_.TauCeti.LSeries.one_div_two_pi_le_one
    nlinarith [_root_.sq_nonneg (_root_.Real.log (t / x) + 1), _root_.mul_le_mul hb1 hb1 hb0.le _root_.zero_le_one]
  intro s hs t ht hst
  exact _root_.inv_anti₀ (_root_.TauCeti.LSeries.logWeight_denom_pos hx hs) (hmono hs ht hst)

private lemma TauCeti.LSeries.logWeight_nonneg (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ _root_.TauCeti.LSeries.logWeight x t := by
  have := hx
  unfold _root_.TauCeti.LSeries.logWeight
  positivity

/-- On a finite interval `[1, T]` the integral of the logarithmic weight is at most `2π²`: its
antiderivative `2π arctan (log (t / x) / 2π)` varies by less than `2π · π`. -/
private lemma TauCeti.LSeries.integral_logWeight_le (hx : 0 < x) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, _root_.TauCeti.LSeries.logWeight x t ≤ 2 * π ^ 2 := by
  have hderiv : ∀ t ∈ _root_.Set.uIcc (1 : ℝ) T, _root_.HasDerivAt
      (fun t ↦ 2 * π * _root_.Real.arctan (1 / (2 * π) * _root_.Real.log (t / x))) (_root_.TauCeti.LSeries.logWeight x t) t := by
    intro t ht
    rw [_root_.Set.uIcc_of_le hT] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ((((_root_.TauCeti.LSeries.hasDerivAt_log_div hx ht0).const_mul (1 / (2 * π))).arctan).const_mul
      (2 * π)).congr_deriv ?_
    simp only [_root_.TauCeti.LSeries.logWeight]
    field_simp
  have hint : _root_.IntervalIntegrable (_root_.TauCeti.LSeries.logWeight x) _root_.MeasureTheory.MeasureSpace.volume 1 T :=
    ((_root_.TauCeti.LSeries.antitoneOn_logWeight hx).mono fun t ht ↦ by
      rw [_root_.Set.uIcc_of_le hT] at ht
      exact _root_.lt_of_lt_of_le _root_.one_pos ht.1).intervalIntegrable
  rw [_root_.intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, ← _root_.mul_sub]
  have h1 := _root_.Real.arctan_lt_pi_div_two (1 / (2 * π) * _root_.Real.log (T / x))
  have h2 := _root_.Real.neg_pi_div_two_lt_arctan (1 / (2 * π) * _root_.Real.log (1 / x))
  nlinarith [_root_.Real.pi_pos]

/-- The weight summed over `1 ≤ n ≤ N` is at most `1 + 2π²`, uniformly in `N` and `x > 0`. -/
private lemma TauCeti.LSeries.sum_range_logWeight_le (hx : 0 < x) (N : ℕ) :
    ∑ i ∈ _root_.Finset.range N, _root_.TauCeti.LSeries.logWeight x (i + 1 : ℕ) ≤ 1 + 2 * π ^ 2 := by
  rcases N with _ | M
  · simp only [_root_.Finset.range_zero, _root_.Finset.sum_empty]
    positivity
  rw [_root_.Finset.sum_range_succ']
  have hfirst : _root_.TauCeti.LSeries.logWeight x ((0 + 1 : ℕ) : ℝ) ≤ 1 := by
    simp only [_root_.TauCeti.LSeries.logWeight, _root_.zero_add, _root_.Nat.cast_one, _root_.one_mul]
    exact _root_.inv_le_one_of_one_le₀ (_root_.le_add_of_nonneg_right (_root_.sq_nonneg _))
  have hanti : _root_.AntitoneOn (_root_.TauCeti.LSeries.logWeight x) (_root_.Set.Icc 1 (1 + (M : ℝ))) :=
    (_root_.TauCeti.LSeries.antitoneOn_logWeight hx).mono fun t ht ↦ _root_.lt_of_lt_of_le _root_.one_pos ht.1
  have hsum := hanti.sum_le_integral
  have hint := _root_.TauCeti.LSeries.integral_logWeight_le hx (T := 1 + M) (by linarith [M.cast_nonneg (α := ℝ)])
  have hrw : ∀ i ∈ _root_.Finset.range M, _root_.TauCeti.LSeries.logWeight x ((i + 1 + 1 : ℕ) : ℝ) =
      _root_.TauCeti.LSeries.logWeight x (1 + ((i + 1 : ℕ) : ℝ)) := fun i _ ↦ by
    push_cast
    ring_nf
  rw [_root_.Finset.sum_congr _root_.rfl hrw]
  linarith

/-! ### The uniform bound -/

/-- The logarithmically weighted norm series, written against the weight. -/
private lemma TauCeti.LSeries.norm_term_mul_inv_one_add_sq_eq (n : ℕ) :
    ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * _root_.Real.log (n / x)) ^ 2)⁻¹ =
      ‖a n‖ * _root_.TauCeti.LSeries.logWeight x n := by
  rcases _root_.eq_or_ne n 0 with rfl | hn
  · simp [_root_.TauCeti.LSeries.logWeight]
  simp only [_root_.LSeries.norm_term_eq, hn, ↓_root_.reduceIte, _root_.Complex.one_re, _root_.Real.rpow_one,
    _root_.TauCeti.LSeries.logWeight, _root_.mul_inv, _root_.div_eq_mul_inv, _root_.mul_assoc]

private lemma TauCeti.LSeries.norm_term_mul_inv_one_add_sq_nonneg (n : ℕ) :
    0 ≤ ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * _root_.Real.log (n / x)) ^ 2)⁻¹ := by
  positivity

/-- The partial sums of the logarithmically weighted norm series are at most `C (1 + 2π²)`. -/
private lemma TauCeti.LSeries.sum_range_norm_term_mul_inv_one_add_sq_le
    (hC : ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, ‖a n‖ ≤ C * N) (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ _root_.Finset.range N,
        ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * _root_.Real.log (n / x)) ^ 2)⁻¹ ≤
      C * (1 + 2 * π ^ 2) := by
  have hC0 : 0 ≤ C := by
    have h := hC 1
    simp only [_root_.Finset.Icc_self, _root_.Finset.sum_singleton, _root_.Nat.cast_one, _root_.mul_one] at h
    exact (_root_.norm_nonneg _).trans h
  -- Enlarge the range by one and drop the vanishing `n = 0` term.
  refine _root_.le_trans (_root_.Finset.sum_le_sum_of_subset_of_nonneg (_root_.Finset.range_subset_range.2 N.le_succ)
    fun n _ _ ↦ _root_.TauCeti.LSeries.norm_term_mul_inv_one_add_sq_nonneg n) ?_
  rw [_root_.Finset.sum_range_succ']
  simp only [_root_.TauCeti.LSeries.norm_term_mul_inv_one_add_sq_eq]
  have hlogWeight_zero : _root_.TauCeti.LSeries.logWeight x ((0 : ℕ) : ℝ) = 0 := by simp [_root_.TauCeti.LSeries.logWeight]
  rw [hlogWeight_zero, _root_.MulZeroClass.mul_zero, _root_.add_zero]
  -- Abel's inequality against the constant sequence `C`.
  have hpartial : ∀ k ≤ N, ∑ i ∈ _root_.Finset.range k, ‖a (i + 1)‖ ≤
      ∑ _i ∈ _root_.Finset.range k, C := fun k _ ↦ by
    rw [_root_.Finset.sum_const, _root_.Finset.card_range, _root_.nsmul_eq_mul, _root_.mul_comm]
    convert hC k using 1
    rw [_root_.Finset.range_eq_Ico, _root_.Finset.sum_Ico_add' (fun n ↦ ‖a n‖) 0 k 1]
    rfl
  have habel := _root_.TauCeti.sum_range_mul_le_sum_range_mul (w := fun i ↦ _root_.TauCeti.LSeries.logWeight x (i + 1 : ℕ)) hpartial
    (fun i _ ↦ _root_.TauCeti.LSeries.antitoneOn_logWeight hx (by simp only [_root_.Set.mem_Ioi]; positivity)
      (by simp only [_root_.Set.mem_Ioi]; positivity) (by push_cast; linarith))
    (_root_.TauCeti.LSeries.logWeight_nonneg hx (_root_.Nat.cast_nonneg _))
  calc ∑ i ∈ _root_.Finset.range N, ‖a (i + 1)‖ * _root_.TauCeti.LSeries.logWeight x (i + 1 : ℕ)
      = ∑ i ∈ _root_.Finset.range N, _root_.TauCeti.LSeries.logWeight x (i + 1 : ℕ) * ‖a (i + 1)‖ :=
        _root_.Finset.sum_congr _root_.rfl fun _ _ ↦ _root_.mul_comm _ _
    _ ≤ ∑ i ∈ _root_.Finset.range N, _root_.TauCeti.LSeries.logWeight x (i + 1 : ℕ) * C := habel
    _ = C * ∑ i ∈ _root_.Finset.range N, _root_.TauCeti.LSeries.logWeight x (i + 1 : ℕ) := by
        rw [_root_.Finset.mul_sum]
        exact _root_.Finset.sum_congr _root_.rfl fun _ _ ↦ _root_.mul_comm _ _
    _ ≤ C * (1 + 2 * π ^ 2) := _root_.mul_le_mul_of_nonneg_left (_root_.TauCeti.LSeries.sum_range_logWeight_le hx N) hC0

/-- Under a Chebyshev bound the logarithmically weighted norm series converges at every scale
`x > 0`. -/
theorem TauCeti.LSeries.summable_norm_term_mul_inv_one_add_sq
    (hC : ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, ‖a n‖ ≤ C * N) (hx : 0 < x) :
    _root_.Summable fun n : ℕ ↦
      ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * _root_.Real.log (n / x)) ^ 2)⁻¹ :=
  _root_.summable_of_sum_range_le (fun _ ↦ _root_.TauCeti.LSeries.norm_term_mul_inv_one_add_sq_nonneg _)
    (_root_.TauCeti.LSeries.sum_range_norm_term_mul_inv_one_add_sq_le hC hx)

/-- **The uniform logarithmic bound.** If `∑_{1 ≤ n ≤ N} ‖a n‖ ≤ C N` for every `N`, then
`∑ ‖a n‖ / n * (1 + (log (n / x) / 2π) ^ 2)⁻¹ ≤ C (1 + 2π²)` for every scale `x > 0`. -/
theorem TauCeti.LSeries.tsum_norm_term_mul_inv_one_add_sq_le
    (hC : ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, ‖a n‖ ≤ C * N) (hx : 0 < x) :
    ∑' n : ℕ, ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * _root_.Real.log (n / x)) ^ 2)⁻¹ ≤
      C * (1 + 2 * π ^ 2) :=
  _root_.Real.tsum_le_of_sum_range_le (fun _ ↦ _root_.TauCeti.LSeries.norm_term_mul_inv_one_add_sq_nonneg _)
    (_root_.TauCeti.LSeries.sum_range_norm_term_mul_inv_one_add_sq_le hC hx)

/-! ### Weights with quadratic decay -/

variable {W : ℝ → ℂ} {M : ℝ}

private lemma TauCeti.LSeries.term_mul_comp_log_div :
    _root_.LSeries.term (fun n ↦ a n * W (1 / (2 * π) * _root_.Real.log (n / x))) 1 =
      fun n ↦ _root_.LSeries.term a 1 n * W (1 / (2 * π) * _root_.Real.log (n / x)) := by
  ext n
  rcases _root_.eq_or_ne n 0 with rfl | hn
  · simp
  rw [_root_.LSeries.term_of_ne_zero hn, _root_.LSeries.term_of_ne_zero hn]
  ring

private lemma TauCeti.LSeries.norm_term_mul_le (hW : ∀ v, ‖W v‖ ≤ M * (1 + v ^ 2)⁻¹) (n : ℕ) :
    ‖_root_.LSeries.term a 1 n * W (1 / (2 * π) * _root_.Real.log (n / x))‖ ≤
      M * (‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * _root_.Real.log (n / x)) ^ 2)⁻¹) := by
  rw [_root_.norm_mul, _root_.mul_left_comm]
  exact _root_.mul_le_mul_of_nonneg_left (hW _) (_root_.norm_nonneg _)

/-- Under a Chebyshev bound, a weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹` gives a Dirichlet series
`∑ a n W (log (n / x) / 2π) n⁻ˢ` that converges at `s = 1`, at every scale `x > 0`. -/
theorem TauCeti.LSeries.LSeriesSummable_mul_comp_log_div
    (hC : ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, ‖a n‖ ≤ C * N)
    (hW : ∀ v, ‖W v‖ ≤ M * (1 + v ^ 2)⁻¹) (hx : 0 < x) :
    _root_.LSeriesSummable (fun n : ℕ ↦ a n * W (1 / (2 * π) * _root_.Real.log (n / x))) 1 := by
  rw [_root_.LSeriesSummable, _root_.TauCeti.LSeries.term_mul_comp_log_div]
  exact ((_root_.TauCeti.LSeries.summable_norm_term_mul_inv_one_add_sq hC hx).mul_left M).of_norm_bounded
    (_root_.TauCeti.LSeries.norm_term_mul_le hW)

/-- **The uniform bound for a decaying weight.** Under a Chebyshev bound
`∑_{1 ≤ n ≤ N} ‖a n‖ ≤ C N`, a weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹` gives
`‖∑ a n / n * W (log (n / x) / 2π)‖ ≤ M C (1 + 2π²)` for every scale `x > 0`. -/
theorem TauCeti.LSeries.norm_tsum_term_mul_comp_log_div_le
    (hC : ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, ‖a n‖ ≤ C * N)
    (hW : ∀ v, ‖W v‖ ≤ M * (1 + v ^ 2)⁻¹) (hx : 0 < x) :
    ‖∑' n : ℕ, _root_.LSeries.term a 1 n * W (1 / (2 * π) * _root_.Real.log (n / x))‖ ≤
      M * (C * (1 + 2 * π ^ 2)) := by
  have hbound := (_root_.TauCeti.LSeries.summable_norm_term_mul_inv_one_add_sq hC hx).mul_left M
  have hnorm := hbound.of_nonneg_of_le (fun _ ↦ _root_.norm_nonneg _) (_root_.TauCeti.LSeries.norm_term_mul_le hW)
  have hM : 0 ≤ M := (_root_.norm_nonneg _).trans ((hW 0).trans (by simp))
  refine (_root_.norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum (_root_.TauCeti.LSeries.norm_term_mul_le hW)
    hbound).trans ?_)
  rw [_root_.tsum_mul_left]
  exact _root_.mul_le_mul_of_nonneg_left (_root_.TauCeti.LSeries.tsum_norm_term_mul_inv_one_add_sq_le hC hx) hM

/-! ### Passing the smoothed asymptotic to approximable weights -/

variable {G : ℂ → ℂ} {A L : ℂ}

/-- **The smoothed Wiener--Ikehara asymptotic for an approximable weight.** Let `a` be
nonnegative, with Dirichlet series summable on `Re s > 1` and a boundary remainder
`G = LSeries a - A / (s - 1)` continuous on `Re s ≥ 1`. Suppose that for every `ε > 0` some smooth
compactly supported `psi` satisfies `‖W v - 𝓕 psi v‖ ≤ ε (1 + v ^ 2)⁻¹` for all `v` and
`‖L - psi 0‖ ≤ ε`. Then `∑ a n / n * W (log (n / x) / 2π) → 2π A L` as `x → ∞`.

For `W = 𝓕 psi` itself this is `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg`
with `L = psi 0`; the point is that `W` need not be the Fourier transform of a compactly
supported function. -/
theorem solution (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = _root_.LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → _root_.LSeriesSummable a sigma)
    (happrox : ∀ ε > 0, ∃ psi : ℝ → ℂ, _root_.ContDiff ℝ ∞ psi ∧ _root_.HasCompactSupport psi ∧
      (∀ v, ‖W v - 𝓕 psi v‖ ≤ ε * (1 + v ^ 2)⁻¹) ∧ ‖L - psi 0‖ ≤ ε) :
    _root_.Filter.Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * W (1 / (2 * π) * _root_.Real.log (n / x)))
      _root_.Filter.atTop (𝓝 (2 * (π : ℂ) * A * L)) := by
  obtain ⟨C₀, hC⟩ :=
    _root_.TauCeti.exists_sum_Icc_le_mul_of_isBigO (_root_.TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary ha hG hG' hsum)
  set C := _root_.Max.max C₀ 0
  replace hC : ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, ‖a n‖ ≤ C * N := fun N ↦
    (hC N).trans (_root_.mul_le_mul_of_nonneg_right (_root_.le_max_left _ _) N.cast_nonneg)
  -- The size of the error: `δ` in the weighted sup norm costs at most `δ K` in the limit.
  set K : ℝ := C * (1 + 2 * π ^ 2) + ‖2 * (π : ℂ) * A‖ + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ C := _root_.le_max_right _ _
    positivity
  rw [_root_.Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨psi, hpsi, hsupp, hW, hL⟩ := happrox (ε / (2 * K)) (by positivity)
  obtain ⟨x₀, hx₀⟩ := _root_.Metric.tendsto_atTop.1
    (_root_.TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg ha hG hG' hsum hpsi hsupp) (ε / 2)
    (by positivity)
  refine ⟨_root_.Max.max x₀ 1, fun x hx ↦ ?_⟩
  have hxpos : 0 < x := _root_.lt_of_lt_of_le _root_.one_pos ((_root_.le_max_right _ _).trans hx)
  have hmain := hx₀ x ((_root_.le_max_left _ _).trans hx)
  -- Split the series into the compactly supported part and the error.
  have hsumpsi : _root_.Summable fun n : ℕ ↦
      _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x)) := by
    have := _root_.TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg (x := x) ha
      (hG.comp Complex.continuous_ofReal.continuousOn fun r hr ↦ by simpa using hr.1)
      (fun sigma h1 _ ↦ hG' sigma (by simpa using h1)) (fun sigma h1 _ ↦ hsum sigma h1)
      hpsi hsupp hxpos
    rwa [_root_.LSeriesSummable, _root_.TauCeti.LSeries.term_mul_comp_log_div] at this
  have hsumerr : _root_.Summable fun n : ℕ ↦ _root_.LSeries.term a 1 n *
      (W (1 / (2 * π) * _root_.Real.log (n / x)) - 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) := by
    have := _root_.TauCeti.LSeries.LSeriesSummable_mul_comp_log_div (W := W - 𝓕 psi) hC hW hxpos
    rw [_root_.LSeriesSummable, _root_.TauCeti.LSeries.term_mul_comp_log_div] at this
    simpa only [_root_.Pi.sub_apply] using this
  have hsplit : ∑' n : ℕ, _root_.LSeries.term a 1 n * W (1 / (2 * π) * _root_.Real.log (n / x)) =
      ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x)) +
        ∑' n : ℕ, _root_.LSeries.term a 1 n *
          (W (1 / (2 * π) * _root_.Real.log (n / x)) - 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) := by
    rw [← hsumpsi.tsum_add hsumerr]
    exact _root_.tsum_congr fun n ↦ by ring
  have herr := _root_.TauCeti.LSeries.norm_tsum_term_mul_comp_log_div_le hC hW hxpos
  have hconst : ‖2 * (π : ℂ) * A * psi 0 - 2 * (π : ℂ) * A * L‖ ≤
      ‖2 * (π : ℂ) * A‖ * (ε / (2 * K)) := by
    rw [← _root_.mul_sub, _root_.norm_mul, _root_.norm_sub_rev]
    exact _root_.mul_le_mul_of_nonneg_left hL (_root_.norm_nonneg _)
  have hsmall : ε / (2 * K) * (C * (1 + 2 * π ^ 2)) + ‖2 * (π : ℂ) * A‖ * (ε / (2 * K)) ≤
      ε / 2 := by
    calc _ = ε / (2 * K) * (C * (1 + 2 * π ^ 2) + ‖2 * (π : ℂ) * A‖) := by ring
      _ ≤ ε / (2 * K) * K := by
          refine _root_.mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hK]
          exact _root_.le_add_of_nonneg_right _root_.zero_le_one
      _ = ε / 2 := by field_simp
  rw [_root_.dist_eq_norm] at hmain ⊢
  rw [hsplit]
  calc
    _ = ‖(∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi
          (1 / (2 * π) * _root_.Real.log (n / x))) - 2 * (π : ℂ) * A * psi 0 +
        ∑' n : ℕ, _root_.LSeries.term a 1 n *
          (W (1 / (2 * π) * _root_.Real.log (n / x)) - 𝓕 psi
            (1 / (2 * π) * _root_.Real.log (n / x))) +
        (2 * (π : ℂ) * A * psi 0 - 2 * (π : ℂ) * A * L)‖ :=
      _root_.congrArg _root_.Norm.norm (by abel)
    _ < ε := by
      refine (norm_add₃_le.trans_lt (_root_.add_lt_add_of_lt_of_le
        (_root_.add_lt_add_of_lt_of_le hmain herr) hconst)).trans_le ?_
      rw [_root_.add_assoc]
      exact (_root_.add_le_add_right hsmall _).trans (_root_.add_halves ε).le

/-! ### Schwartz test functions -/



end TauCeti.LSeries

end
end
