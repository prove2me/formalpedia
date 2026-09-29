-- Prove2me | solution 1 for Zeta23.PX_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:56:11.310668+00:00
-- url     : https://prove2.me/submissions/ee967af2-5a68-4b21-8c25-2f90d2b89d3c

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
open ArithmeticFunction

theorem solution (X τ : ℝ) :
    |PX X τ| ≤ (1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, vonMangoldt n / Real.sqrt n := by
  unfold PX
  rw [neg_mul, abs_neg, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, vonMangoldt n / Real.sqrt n * Real.cos (τ * Real.log n)|
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, |vonMangoldt n / Real.sqrt n * Real.cos (τ * Real.log n)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, vonMangoldt n / Real.sqrt n := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [abs_mul, abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))]
        have h2 : |Real.cos (τ * Real.log n)| ≤ 1 := Real.abs_cos_le_one _
        have h3 : (0 : ℝ) ≤ vonMangoldt n / Real.sqrt n :=
          div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
        nlinarith
