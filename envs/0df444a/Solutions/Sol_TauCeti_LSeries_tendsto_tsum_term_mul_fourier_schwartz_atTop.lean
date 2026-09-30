-- Prove2me | solution 1 for TauCeti.LSeries.tendsto_tsum_term_mul_fourier_schwartz_atTop
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:13:21.580891+00:00
-- url     : https://prove2.me/submissions/266210ff-1d62-4bc4-a5ee-cfb682fe73ec

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
import Theorems.Thm_SchwartzMap_tendsto_smulLeftCLM_comp_inv_smul_atTop
import Theorems.Thm_TauCeti_LSeries_tendsto_tsum_term_mul_atTop_of_approx_fourier

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cutting off a Schwartz function

Let `χ : E → ℝ` be a smooth compactly supported function that equals `1` near the origin. For a
Schwartz function `f`, the truncations `x ↦ χ (R⁻¹ • x) • f x` are smooth and compactly supported,
and they converge to `f` in the Schwartz topology as `R → ∞`. Consequently the smooth compactly
supported functions are dense in `𝓢(E, F)` when `E` is finite-dimensional.

This is how a statement proved for smooth compactly supported test functions is passed to Schwartz
test functions: any quantity controlled by finitely many Schwartz seminorms (for instance a
weighted sup norm of the Fourier transform) is approximated by its values on the truncations.

The estimate is explicit. Suppose `χ = 1` on the ball of radius `r` and `R ≥ 1`. The difference
`f - χ (R⁻¹ • ·) • f` is `(1 - χ (R⁻¹ • ·)) • f`, which vanishes on the ball of radius `r R`.
Expand its `n`-th derivative by the Leibniz rule. The term in which no derivative falls on the
cutoff is supported where `‖x‖ ≥ r R`, so trading one power of `‖x‖` against `(r R)⁻¹` bounds it by
the `(k + 1, n)` seminorm of `f` divided by `r R`. Every other term carries a derivative of
`χ (R⁻¹ • ·)` of order `i ≥ 1`, which is `R⁻ⁱ` times a derivative of `χ` and hence `O(R⁻¹)`.
Altogether the `(k, n)` seminorm of the difference is `O(R⁻¹)`.

## Main results

* `SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le`: the explicit bound
  `seminorm k n (f - χ (R⁻¹ • ·) • f) ≤ K / R` for `R ≥ 1`.
* `SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`: the truncations converge to `f` in
  `𝓢(E, F)`.
* `SchwartzMap.hasCompactSupport_smulLeftCLM_comp_inv_smul`: the truncations are compactly
  supported.
* `SchwartzMap.dense_hasCompactSupport`: compactly supported functions are dense in
  `𝓢(E, F)` for finite-dimensional `E`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Section 7.1.
-/

 section

open Filter Metric Set
open scoped ContDiff Topology SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace SchwartzMap

variable {χ : E → ℝ}

/-- The truncation `χ (R⁻¹ • ·) • f` of a Schwartz function by a cutoff of temperate growth,
evaluated pointwise. -/
@[simp]
theorem smulLeftCLM_comp_inv_smul_apply (hχ : χ.HasTemperateGrowth) (R : ℝ) (f : 𝓢(E, F))
    (x : E) : smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f x = χ (R⁻¹ • x) • f x :=
  smulLeftCLM_apply_apply (hχ.comp (R⁻¹ • ContinuousLinearMap.id ℝ E).hasTemperateGrowth) f x

/-- A truncation of a Schwartz function by a compactly supported cutoff is compactly supported. -/
theorem hasCompactSupport_smulLeftCLM_comp_inv_smul (hχ : ContDiff ℝ ∞ χ)
    (hsupp : HasCompactSupport χ) {R : ℝ} (hR : R ≠ 0) (f : 𝓢(E, F)) :
    HasCompactSupport (smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) := by
  rw [funext (smulLeftCLM_comp_inv_smul_apply (hsupp.hasTemperateGrowth hχ) R f)]
  exact (hsupp.comp_smul (inv_ne_zero hR)).smul_right













end SchwartzMap

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





















/-! ### The uniform bound -/











/-! ### Weights with quadratic decay -/

variable {W : ℝ → ℂ} {M : ℝ}









/-! ### Passing the smoothed asymptotic to approximable weights -/

variable {G : ℂ → ℂ} {A L : ℂ}



/-! ### Schwartz test functions -/

/-- **The smoothed Wiener--Ikehara asymptotic for a Schwartz test function.** Let `a` be
nonnegative, with Dirichlet series summable on `Re s > 1` and a boundary remainder
`G = LSeries a - A / (s - 1)` continuous on `Re s ≥ 1`. For every Schwartz function `g` on `ℝ`,
`∑ a n / n * 𝓕 g (log (n / x) / 2π) → 2π A g 0` as `x → ∞`.

This extends `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg` from smooth
compactly supported test functions to Schwartz functions. In particular it applies to every
smooth compactly supported weight `W`, since `W = 𝓕 (𝓕⁻ W)` with `𝓕⁻ W` a Schwartz function. -/
theorem solution (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = _root_.LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → _root_.LSeriesSummable a sigma) (g : 𝓢(ℝ, ℂ)) :
    _root_.Filter.Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 (g : ℝ → ℂ) (1 / (2 * π) * _root_.Real.log (n / x)))
      _root_.Filter.atTop (𝓝 (2 * (π : ℂ) * A * g 0)) := by
  refine _root_.TauCeti.LSeries.tendsto_tsum_term_mul_atTop_of_approx_fourier ha hG hG' hsum fun ε hε ↦ ?_
  -- Truncate `g` by a bump function rescaled by `R`; the truncations tend to `g` in `𝓢(ℝ, ℂ)`,
  -- hence so do their Fourier transforms.
  let b : _root_.ContDiffBump (0 : ℝ) := ⟨1, 2, _root_.one_pos, _root_.one_lt_two⟩
  set u : ℝ → 𝓢(ℝ, ℂ) := fun R ↦ _root_.SchwartzMap.smulLeftCLM ℂ (fun y ↦ b (R⁻¹ • y)) g
  have hbdd (i : ℕ) : ∃ B, ∀ x, ‖_root_.iteratedFDeriv ℝ i b x‖ ≤ B :=
    (b.contDiff.continuous_iteratedFDeriv (mod_cast _root_.le_top)).bounded_above_of_compact_support
      (b.hasCompactSupport.iteratedFDeriv i)
  have hu : _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 g) := _root_.SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop
    b.contDiff hbdd b.eventuallyEq_one g
  have hFu : _root_.Filter.Tendsto (fun R ↦ 𝓕 (u R)) _root_.Filter.atTop (𝓝 (𝓕 g)) :=
    (ContinuousFourier.continuous_fourier.tendsto g).comp hu
  rw [(_root_.schwartz_withSeminorms ℝ ℝ ℂ).tendsto_nhds] at hFu
  obtain ⟨R, hR, h0, h2⟩ := ((_root_.Filter.eventually_gt_atTop 0).and ((hFu (0, 0) (ε / 2) (_root_.half_pos hε)).and
    (hFu (2, 0) (ε / 2) (_root_.half_pos hε)))).exists
  simp only [_root_.SchwartzMap.schwartzSeminormFamily_apply] at h0 h2
  refine ⟨u R, (u R).smooth ⊤, _root_.SchwartzMap.hasCompactSupport_smulLeftCLM_comp_inv_smul
    b.contDiff b.hasCompactSupport hR.ne' g, fun v ↦ ?_, ?_⟩
  · -- The weighted sup norm of `𝓕 g - 𝓕 (u R)` is at most two seminorms of it.
    have hv0 := _root_.SchwartzMap.norm_le_seminorm ℝ (𝓕 (u R) - 𝓕 g) v
    have hv2 := _root_.SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 (u R) - 𝓕 g) 2 v
    rw [_root_.sub_apply, _root_.SchwartzMap.fourier_coe, _root_.SchwartzMap.fourier_coe, _root_.norm_sub_rev] at hv0 hv2
    rw [_root_.Real.norm_eq_abs, _root_.sq_abs] at hv2
    rw [_root_.le_mul_inv_iff₀ (by positivity)]
    linarith
  · -- The truncation does not change the value at the origin.
    rw [_root_.SchwartzMap.smulLeftCLM_comp_inv_smul_apply
        (b.hasCompactSupport.hasTemperateGrowth b.contDiff),
      _root_.smul_zero, b.one_of_mem_closedBall (by simp [b]), _root_.one_smul, _root_.sub_self, _root_.norm_zero]
    exact hε.le

end TauCeti.LSeries

end
end
