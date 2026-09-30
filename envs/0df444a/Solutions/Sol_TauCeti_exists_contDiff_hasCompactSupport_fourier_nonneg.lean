-- Prove2me | solution 1 for TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:36:21.893236+00:00
-- url     : https://prove2.me/submissions/2c3ffca8-965b-4348-8f69-c4ea62e40605

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Theorems.Thm_TauCeti_fourier_im_eq_zero_of_map_neg_eq_conj

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonnegativity of the Fourier transform of a positive-definite function

For a continuous, integrable function `F : V → ℂ` on a finite-dimensional real inner-product
space whose subtraction kernel `(a, b) ↦ F (a - b)` is positive definite, the Fourier transform
`𝓕 F` is real and nonnegative: its real part is nonnegative at every frequency and its imaginary
part vanishes. This is the analytic half of Bochner's theorem.

The real-part nonnegativity is proved by Fejér ball averaging. For a fixed frequency `ξ`, the
twisted function `ψ = fourierAtom ξ * F` is still positive definite (Schur product with the
Fourier atom kernel), continuous, and integrable, and `𝓕 F ξ = ∫ ψ`. For `R > 0` the averaged
double integral `J_R = vol(B_R)⁻¹ ∬_{B_R × B_R} ψ (x - y)` has nonnegative real part because it
is a limit of positive-definite double sums (simple-function approximation of the identity),
while Fubini rewrites `J_R = ∫ ψ · overlapRatio R` whose dominated limit as `R → ∞` is `∫ ψ`.

Building on this, the Fourier transform of such a function is itself *integrable*: testing
against a shrinking family of Gaussians and using the Parseval/Fubini identity bounds
`∫ (𝓕 F) · exp (-t‖·‖²)` by `(F 0).re` uniformly in `t`, and Fatou's lemma passes to the limit.

Adapted (Apache 2.0) from the Bochner–Minlos formalization by Michael R. Douglas
(https://github.com/mrdouglasny/bochner, revision `08eb302`), source files `Bochner/FejerPD.lean`
and `Bochner/Main.lean`; the arguments are ported with the positive-definiteness hypotheses
restated through `Matrix.PosSemidef`.

## Main declarations

* `TauCeti.fourier_re_nonneg_of_posSemidef`: the Fourier transform of a
  continuous integrable positive-definite function has nonnegative real part.
* `TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj` and
  `TauCeti.fourier_eq_re_of_map_neg_eq_conj`: for an integrable *conjugate-symmetric* `F`
  (continuity is not needed), the imaginary part of `𝓕 F` vanishes and `𝓕 F` equals its own real
  part; `TauCeti.fourier_im_eq_zero_of_posSemidef` and
  `TauCeti.fourier_eq_re_of_posSemidef` are the positive-definite specializations.
* `TauCeti.integrable_fourier_of_posSemidef`: the Fourier transform of a
  continuous integrable positive-definite function is integrable.
* `TauCeti.fourierInv_re_nonneg_of_posSemidef`,
  `TauCeti.fourierInv_eq_re_of_posSemidef`,
  `TauCeti.integrable_fourierInv_of_posSemidef` and
  `TauCeti.measurable_ofReal_re_fourierInv`: the same facts for the inverse transform `𝓕⁻ F`,
  which is the density of the representing measure of Bochner's theorem.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), Theorem 1.4.3.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §4.2, Lemma 4.8.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

 section

open Complex ComplexConjugate Filter MeasureTheory
open scoped ComplexOrder FourierTransform Topology

namespace TauCeti

/-! ### A simple-function expansion for integrals of compositions -/

section SimpleFuncExpansion

variable {α : Type*} [MeasurableSpace α]







end SimpleFuncExpansion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Consequences of positive definiteness for a subtraction kernel -/

section KernelConsequences

variable {ψ : V → ℂ}



end KernelConsequences

/-! ### Step A: the positive-definite double integral has nonnegative real part -/







/-! ### The Fejér overlap ratio -/















/-! ### Step B: the Fubini identity for the Fejér average -/













/-! ### Step C: the integral of a positive-definite function has nonnegative real part -/





/-! ### The main theorems -/





/-- The Fourier transform of an integrable conjugate-symmetric function on a finite-dimensional
real inner-product space is real: it equals the coercion of its own real part.

As in `fourier_im_eq_zero_of_map_neg_eq_conj`, `hint` is a design choice rather than a proof
obligation — it is used only to discharge that lemma, which is itself provable without it. It is
required here so that the conclusion cannot be read off a divergent integral's default value. -/
theorem fourier_eq_re_of_map_neg_eq_conj (F : V → ℂ)
    (hsymm : ∀ v : V, F (-v) = conj (F v)) (hint : Integrable F) (ξ : V) :
    𝓕 F ξ = ((𝓕 F ξ).re : ℂ) := by
  refine Complex.ext (by simp) ?_
  simp [fourier_im_eq_zero_of_map_neg_eq_conj F hsymm hint ξ]





/-! ### Integrability of the Fourier transform of a positive-definite function -/













/-! ### The inverse transform

The inverse Fourier transform `𝓕⁻ F = 𝓕 F ∘ (-·)` is the density of the representing measure of
Bochner's theorem, so nonnegativity, realness and integrability are recorded for it too. -/











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
# A smooth compactly supported function with nonnegative Fourier transform

On a finite-dimensional real inner-product space there is a smooth, compactly supported function
`psi` whose Fourier transform is real and nonnegative everywhere and strictly positive at the
origin. Such a test function turns a limit statement about a Fourier-weighted sum with nonnegative
summands into an upper bound on the summands near the origin of the frequency variable, which is
how Tauberian arguments extract a Chebyshev-type growth bound from smoothed asymptotics.

The function is the autocorrelation `g ⋆ g` of a real bump function `g`. The bump function is even
and real, so its Fourier transform is real
(`TauCeti.fourier_eq_re_of_map_neg_eq_conj`), and the Fourier transform of the convolution is
the square of that real number (`Real.fourier_mul_convolution_eq`). At the origin it is the square
of `∫ g`, which is positive.

## Main results

* `TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg`: a smooth compactly supported
  function whose Fourier transform is nonnegative everywhere and positive at `0`.
-/

 section

open Complex MeasureTheory
open scoped ComplexOrder ContDiff Convolution FourierTransform

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- There is a smooth compactly supported complex-valued function on `V` whose Fourier transform
is nonnegative (in `ComplexOrder`, so real and nonnegative) at every frequency and strictly
positive at the origin. -/
theorem solution :
    ∃ psi : V → ℂ, _root_.ContDiff ℝ ∞ psi ∧ _root_.HasCompactSupport psi ∧
      (∀ ξ : V, 0 ≤ 𝓕 psi ξ) ∧ 0 < 𝓕 psi 0 := by
  let φ : _root_.ContDiffBump (0 : V) := ⟨1, 2, _root_.one_pos, _root_.one_lt_two⟩
  let g : V → ℂ := fun v ↦ (φ v : ℂ)
  have hg : _root_.ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hgc : _root_.HasCompactSupport g := φ.hasCompactSupport.comp_left _root_.Complex.ofReal_zero
  have hgi : _root_.MeasureTheory.Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hre : ∀ ξ : V, 𝓕 g ξ = ((𝓕 g ξ).re : ℂ) :=
    _root_.TauCeti.fourier_eq_re_of_map_neg_eq_conj g (fun v ↦ by simp [g, φ.neg]) hgi
  have hsq : ∀ ξ : V, 𝓕 (g ⋆[_root_.ContinuousLinearMap.mul ℂ ℂ] g) ξ =
      (((𝓕 g ξ).re * (𝓕 g ξ).re : ℝ) : ℂ) := fun ξ ↦ by
    rw [_root_.Real.fourier_mul_convolution_eq hgi hgi, hre, _root_.Complex.ofReal_mul, _root_.Complex.ofReal_re]
  have h0 : (𝓕 g 0).re = ∫ v, φ v := by
    have : 𝓕 g 0 = ((∫ v, φ v : ℝ) : ℂ) := by
      simp only [_root_.Real.fourier_eq, _root_.inner_zero_right, _root_.neg_zero, _root_.AddChar.map_zero_eq_one, _root_.one_smul, g]
      exact _root_.integral_ofReal
    rw [this, _root_.Complex.ofReal_re]
  have hconv : g ⋆[_root_.ContinuousLinearMap.mul ℂ ℂ] g = g ⋆[_root_.ContinuousLinearMap.mul ℝ ℂ] g := by
    ext v
    simp [_root_.MeasureTheory.convolution_def]
  refine ⟨g ⋆[_root_.ContinuousLinearMap.mul ℂ ℂ] g, ?_, hgc.convolution _ hgc, fun ξ ↦ ?_, ?_⟩
  · rw [hconv]
    exact hgc.contDiff_convolution_left _ hg hgi.locallyIntegrable
  · rw [hsq, _root_.Complex.zero_le_real]
    exact _root_.mul_self_nonneg _
  · rw [hsq, _root_.Complex.zero_lt_real, h0]
    exact _root_.mul_pos φ.integral_pos φ.integral_pos

end TauCeti

end
end
