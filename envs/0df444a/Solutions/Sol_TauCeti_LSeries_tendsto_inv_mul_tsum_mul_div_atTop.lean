-- Prove2me | solution 1 for TauCeti.LSeries.tendsto_inv_mul_tsum_mul_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:17:34.325764+00:00
-- url     : https://prove2.me/submissions/23cf65ba-0680-4527-b631-9705024b0470

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_LSeries_WienerIkehara_SharpCutoff
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
import Theorems.Thm_TauCeti_LSeries_tendsto_tsum_term_mul_fourier_schwartz_atTop

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



private lemma TauCeti.LSeries.contDiff_expWeight (hΨ : _root_.ContDiff ℝ ∞ Ψ) : _root_.ContDiff ℝ ∞ (_root_.TauCeti.LSeries.expWeight Ψ) := by
  have he : _root_.ContDiff ℝ ∞ fun v : ℝ ↦ _root_.Real.exp (2 * π * v) := by fun_prop
  exact he.smul (hΨ.comp he)

/-- A compact support inside `(0, ∞)` becomes a compact support after the substitution
`y = e^{2πv}`: it is the image of `tsupport Ψ` under `y ↦ log y / 2π`. -/
private lemma TauCeti.LSeries.hasCompactSupport_expWeight (hΨc : _root_.HasCompactSupport Ψ)
    (hΨpos : _root_.tsupport Ψ ⊆ _root_.Set.Ioi 0) : _root_.HasCompactSupport (_root_.TauCeti.LSeries.expWeight Ψ) := by
  refine _root_.HasCompactSupport.intro (K := (fun y ↦ _root_.Real.log y / (2 * π)) '' _root_.tsupport Ψ)
    (hΨc.isCompact.image_of_continuousOn fun y hy ↦
      ((_root_.Real.continuousAt_log (hΨpos hy).ne').div_const _).continuousWithinAt) fun v hv ↦ ?_
  by_contra h
  refine hv ⟨_root_.Real.exp (2 * π * v), _root_.subset_tsupport _ fun h0 ↦ h ?_, ?_⟩
  · simp [_root_.TauCeti.LSeries.expWeight, h0]
  · simp only [_root_.Real.log_exp]
    field_simp

private lemma TauCeti.LSeries.term_mul_expWeight (a : ℕ → ℂ) (hΨ0 : Ψ 0 = 0) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    _root_.LSeries.term a 1 n * _root_.TauCeti.LSeries.expWeight Ψ (1 / (2 * π) * _root_.Real.log (n / x)) =
      (x : ℂ)⁻¹ * (a n * Ψ (n / x)) := by
  rcases _root_.eq_or_ne n 0 with rfl | hn
  · simp [hΨ0]
  have hn' : (0 : ℝ) < n := by positivity
  have hexp : _root_.Real.exp (2 * π * (1 / (2 * π) * _root_.Real.log (n / x))) = n / x := by
    rw [← _root_.mul_assoc, _root_.mul_one_div_cancel (by positivity), _root_.one_mul, _root_.Real.exp_log (by positivity)]
  rw [_root_.LSeries.term_of_ne_zero hn, _root_.TauCeti.LSeries.expWeight, hexp, _root_.Complex.cpow_one, _root_.Complex.real_smul]
  push_cast
  field_simp

/-- The substitution `y = e^{2πv}`: `∫ W = (2π)⁻¹ ∫_{(0, ∞)} Ψ`. -/
private lemma TauCeti.LSeries.integral_expWeight :
    ∫ v, _root_.TauCeti.LSeries.expWeight Ψ v = (2 * π : ℂ)⁻¹ * ∫ y in _root_.Set.Ioi 0, Ψ y := by
  have h := _root_.MeasureTheory.Measure.integral_comp_mul_left (fun u ↦ _root_.Real.exp u • Ψ (_root_.Real.exp u)) (2 * π)
  have hexp : (∫ u : ℝ, _root_.Real.exp u • Ψ (_root_.Real.exp u)) = ∫ y in _root_.Set.Ioi 0, Ψ y := by
    simpa only [_root_.Set.image_univ, _root_.Real.range_exp, _root_.MeasureTheory.setIntegral_univ] using
      (_root_.MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn _root_.MeasurableSet.univ
        (fun x _ ↦ (_root_.Real.hasDerivAt_exp x).hasDerivWithinAt)
        (Real.exp_monotone.monotoneOn _) Ψ).symm
  simp only [_root_.TauCeti.LSeries.expWeight]
  rw [h, hexp, _root_.abs_of_pos (by positivity), _root_.Complex.real_smul]
  push_cast
  rfl

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ}

/-- **The smoothed Wiener--Ikehara asymptotic for a cutoff on `(0, ∞)`.** Let `a` be
nonnegative, with Dirichlet series summable on `Re s > 1` and a boundary remainder
`G = LSeries a - A / (s - 1)` continuous on `Re s ≥ 1`. For every smooth `Ψ` whose support is a
compact subset of `(0, ∞)`, `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ` as `x → ∞`. -/
theorem solution (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = _root_.LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → _root_.LSeriesSummable a sigma)
    (hΨ : _root_.ContDiff ℝ ∞ Ψ) (hΨc : _root_.HasCompactSupport Ψ) (hΨpos : _root_.tsupport Ψ ⊆ _root_.Set.Ioi 0) :
    _root_.Filter.Tendsto (fun x : ℝ ↦ (x : ℂ)⁻¹ * ∑' n : ℕ, a n * Ψ (n / x)) _root_.Filter.atTop
      (𝓝 (A * ∫ y in _root_.Set.Ioi 0, Ψ y)) := by
  set W : 𝓢(ℝ, ℂ) := (_root_.TauCeti.LSeries.hasCompactSupport_expWeight hΨc hΨpos).toSchwartzMap
    (_root_.TauCeti.LSeries.contDiff_expWeight hΨ)
  have hFg : 𝓕 ((𝓕⁻ W : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = _root_.TauCeti.LSeries.expWeight Ψ := by
    rw [← _root_.SchwartzMap.fourier_coe, _root_.FourierInvPair.fourier_fourierInv_eq]
    rfl
  have hg0 : (𝓕⁻ W : 𝓢(ℝ, ℂ)) 0 = (2 * π : ℂ)⁻¹ * ∫ y in _root_.Set.Ioi 0, Ψ y := by
    rw [_root_.SchwartzMap.fourierInv_coe, _root_.Real.fourierInv_eq, ← _root_.TauCeti.LSeries.integral_expWeight]
    simp [W]
  have hΨ0 : Ψ 0 = 0 := _root_.image_eq_zero_of_notMem_tsupport fun h ↦ _root_.lt_irrefl (0 : ℝ) (hΨpos h)
  have key := _root_.TauCeti.LSeries.tendsto_tsum_term_mul_fourier_schwartz_atTop ha hG hG' hsum (𝓕⁻ W)
  have hscale : 2 * (π : ℂ) * A * ((2 * π : ℂ)⁻¹ * ∫ y in _root_.Set.Ioi 0, Ψ y) =
      A * ∫ y in _root_.Set.Ioi 0, Ψ y := by
    field_simp
  rw [hFg, hg0, hscale] at key
  refine key.congr' ?_
  filter_upwards [_root_.Filter.eventually_gt_atTop 0] with x hx
  simp_rw [_root_.TauCeti.LSeries.term_mul_expWeight a hΨ0 hx, _root_.tsum_mul_left]

end Smooth

/-! ### Bump functions on the positive half-line -/

section Bump

variable {c : ℝ} (φ : ContDiffBump c)









end Bump

/-! ### The sharp cutoff -/

section Sharp

variable {a : ℕ → ℝ} {F G : ℂ → ℂ} {κ : ℝ}













end Sharp

end TauCeti.LSeries

end
end
