-- Prove2me | solution 1 for TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:23:41.830088+00:00
-- url     : https://prove2.me/submissions/48671a67-5d4b-44c1-9330-a7fa7ff829eb

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_PositiveDefinite_FourierAtom
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Order
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

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Fourier atoms

This file records the spatial Fourier atom used by the positive-definite and Bochner APIs.
It uses Mathlib's `2π` Fourier convention.

## Main declarations

* `TauCeti.fourierAtom`: the spatial atom `v ↦ exp (-2πi⟪v, q⟫)`.
* `TauCeti.posSemidef_fourierAtom`: the subtraction kernel attached to a
  Fourier atom is positive definite.
* `TauCeti.continuous_fourierAtom`: Fourier atoms are continuous in the spatial variable.
* `TauCeti.norm_fourierAtom`: Fourier atoms have unit norm.
* `TauCeti.integrable_fourierAtom`: Fourier atoms are integrable against a finite measure.
* `TauCeti.fourierAtom_zero_left` and `TauCeti.fourierAtom_zero_right`: a Fourier atom is `1`
  when either argument is `0`.
-/

 section

open Complex ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]



/-- The `Real.fourierChar` form of a Fourier atom. -/
theorem fourierAtom_eq_fourierChar (q : V) (v : V) :
    fourierAtom q v = (Real.fourierChar (-(inner ℝ v q)) : ℂ) :=
  by simp [fourierAtom]

















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
# Fourier-convention characteristic functions

Mathlib's characteristic function of a finite measure is
`t ↦ ∫ x, exp (⟪x, t⟫ * I) ∂μ`, while the Fourier side of the Bochner roadmap uses the
`2π` convention `a ↦ ∫ q, exp (-2πi⟪a, q⟫) ∂μ`. This file records the conversion between these
normalizations and then reuses the existing characteristic-function API to show that the
Fourier-convention transform of a finite measure is continuous and positive definite.

The file also bridges Mathlib's Fourier transform `𝓕` to the Fourier atom, and it carries the
measure-uniqueness theorem — the uniqueness half of Bochner's theorem — consumed by
`BochnerTheorem.lean`. The convention-free continuity of `𝓕` and `𝓕⁻` lives in
`TauCeti.Analysis.Fourier.Continuous`.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the positive-definite
function API item asking for "a stated Fourier-convention conversion lemma between Mathlib's
`2π` form and the characteristic-function form" before Bochner's theorem.

## Main declarations

* `TauCeti.integral_fourierAtom_eq_charFun_neg_two_pi_smul`: the Fourier-convention integral is
  `charFun μ ((-2π) • a)`.
* `TauCeti.fourier_eq_integral_fourierAtom_mul`: the Fourier transform `𝓕 F` is the
  integral of `F` against the Fourier atom.
* `TauCeti.posSemidef_fourierConventionCharFun_sub`: the Fourier-convention
  translation-invariant kernel of a finite measure is positive definite.
* `TauCeti.Measure.ext_of_forall_integral_fourierAtom_eq`: a finite measure is determined by its
  Fourier-convention transform — the uniqueness half of Bochner's theorem.

## References

* Mathlib's `MeasureTheory.charFun` and Fourier transform convention in
  `Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic` and
  `Mathlib.Analysis.Fourier.FourierTransform`.
-/

 section

open MeasureTheory Complex
open scoped ComplexOrder FourierTransform

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] {μ : Measure V}







section FourierIntegral

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]

/-- The Fourier transform written as the integral against the Fourier atom. -/
theorem fourier_eq_integral_fourierAtom_mul (F : U → ℂ) (ξ : U) :
    𝓕 F ξ = ∫ v, fourierAtom ξ v * F v := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul, fourierAtom_eq_fourierChar]

end FourierIntegral

variable {W : Type*} [SeminormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace W] [OpensMeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]





section Topology

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] {ν : Measure W} [IsFiniteMeasure ν]



end Topology

section Uniqueness

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [SecondCountableTopology W] [CompleteSpace W]



end Uniqueness

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
end TauCeti
section TauCeti
open TauCeti

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



/-- The Fourier transform of an integrable function whose subtraction kernel is positive definite,
on a finite-dimensional real inner-product space, has vanishing imaginary part — by Hermitian
symmetry and the negation invariance of Haar measure.

The argument never uses `_hint`, and the statement is provable without it: each step —
`Real.fourier_eq`, `integral_conj`, `integral_neg_eq_self` — is an equality that survives a
divergent integral, both sides then being the default value `0`. So requiring integrability is a
deliberate design choice, not a proof obligation. Without it `𝓕 F` is that default value rather
than the Fourier transform, so on a non-integrable conjugate-symmetric function such as `F = 1`
the conclusion degenerates to `(0 : ℂ).im = 0`; keeping those vacuous instances out of the public
API is worth the strength given up. Hence the hypothesis is bound as `_hint`.

Not a `@[simp]` lemma: neither side condition is dischargeable by `simp`'s discharger, so the
rule would be tried against every `(𝓕 _ _).im` and never fire. -/
theorem solution (F : V → ℂ)
    (hsymm : ∀ v : V, F (-v) = conj (F v)) (_hint : _root_.MeasureTheory.Integrable F) (ξ : V) :
    (𝓕 F ξ).im = 0 := by
  rw [_root_.TauCeti.fourier_eq_integral_fourierAtom_mul F ξ]
  have hconj : conj (∫ v, _root_.TauCeti.fourierAtom ξ v * F v) = ∫ v, _root_.TauCeti.fourierAtom ξ v * F v := by
    rw [← _root_.integral_conj]
    have hpt : ∀ v : V, conj (_root_.TauCeti.fourierAtom ξ v * F v) = _root_.TauCeti.fourierAtom ξ (-v) * F (-v) := by
      intro v
      rw [_root_.map_mul, ← hsymm v]
      congr 1
      rw [_root_.TauCeti.fourierAtom_eq_fourierChar, _root_.TauCeti.fourierAtom_eq_fourierChar,
        _root_.Circle.starRingEnd_addChar]
      simp [_root_.inner_neg_left]
    simp_rw [hpt]
    exact _root_.MeasureTheory.integral_neg_eq_self (fun v => _root_.TauCeti.fourierAtom ξ v * F v) _root_.MeasureTheory.MeasureSpace.volume
  have him := _root_.congrArg _root_.Complex.im hconj
  simp only [_root_.Complex.conj_im] at him
  linarith







/-! ### Integrability of the Fourier transform of a positive-definite function -/













/-! ### The inverse transform

The inverse Fourier transform `𝓕⁻ F = 𝓕 F ∘ (-·)` is the density of the representing measure of
Bochner's theorem, so nonnegativity, realness and integrability are recorded for it too. -/











end TauCeti

end
end
