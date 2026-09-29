-- Prove2me | solution 1 for Zeta23.PiX_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:52:23.312557+00:00
-- url     : https://prove2.me/submissions/368dee36-cd5d-4b4a-b46d-ffc01ae4b8d6

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses

-- from Zeta23.PiFacts
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PiFacts.lean — [eq:PiPfacts], first clause: the pointwise bound for the
pole density Π_X of [eq:Pidef],

    "|Π_X(τ)| ≤ 3√X/(1+|τ|)"        (the paper, [eq:PiPfacts])

proved here for all X ≥ 1 (the paper applies it with X = e^L → ∞, so any
threshold suffices; no threshold is needed), together with continuity of
Π_X(·) (consumed for integrability).  Consumer: Zeta23/PrimeSideA.lean
(LocalHyps.PiX_bound).

Key inequalities: (1+|τ|)² ≤ 5(1/4+τ²) (so 1/|s| ≤ √5/(1+|τ|) for s = ½+iτ),
|X^s − 1| ≤ √X + 1 ≤ 2√X, and 5/(2π) + 2√5/π < 3.
-/

namespace Zeta23

open Real




/-! ### [eq:Bdef]: the pointwise bound |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X

Paper (after [eq:deltan]): "We shall use the following pointwise bound for ν_X.
By (eq:mufacts), (eq:PiPfacts) and (eq:cheb1), for T ≥ T₀,
  |ν_X(τ)| ≤ B + log⁺(|τ|/4T)  (τ ∈ ℝ),  |ν_X(τ)| ≤ B  (|τ| ≤ 4T),
  B := l + 4√X,  B² ≪ l² + X."                                        [eq:Bdef]

The μ-part consumes the H-Γ fields, so these lemmas take
hΓ : GammaFacts as a hypothesis — conditional on H-Γ exactly as the paper's §5.
The P_X-part uses the Chebyshev bound Zeta23.Cheb.chebyshevMertens.cheb1b
(paper's literal Σ_{n≤X} Λ(n)/√n ≤ 3√X for X ≥ x₀, absorbed into T₀), so no
Chebyshev hypothesis is needed. -/

section NuBound






end NuBound

end Zeta23
open Zeta23
open Real

theorem solution {X : ℝ} (hX : 0 < X) : Continuous (PiX X) := by
  have hXc0 : (X : ℂ) ≠ 0 := by
    exact_mod_cast hX.ne'
  have hscont : Continuous fun τ : ℝ => (1 / 2 + Complex.I * (τ : ℂ)) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hsne : ∀ τ : ℝ, (1 / 2 + Complex.I * (τ : ℂ)) ≠ 0 := by
    intro τ h
    have hre := congrArg Complex.re h
    simp at hre
  unfold PiX
  simp only []
  refine Continuous.add ?_ ?_
  · refine Continuous.div continuous_const ?_ fun τ => ?_
    · exact continuous_const.mul (continuous_const.add (continuous_pow 2))
    · positivity
  · refine continuous_const.mul (Complex.continuous_re.comp ?_)
    refine Continuous.div ?_ hscont hsne
    exact (hscont.const_cpow (Or.inl hXc0)).sub continuous_const
