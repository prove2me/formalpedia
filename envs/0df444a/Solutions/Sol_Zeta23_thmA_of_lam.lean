-- Prove2me | solution 1 for Zeta23.thmA_of_lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:56:44.730201+00:00
-- url     : https://prove2.me/submissions/fff04641-51c7-4e2b-bd17-7043e9aaa658

import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Defs_Profile
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Main
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Definitions.Def_Zeta23_Taper_Basic
import Definitions.Def_Zeta23_Taper_Params
import Definitions.Def_Zeta23_TracesBoundsE
import Definitions.Def_Zeta23_ZeroSide
import Definitions.Def_Zeta23_ZetaReflect
import Theorems.Thm_Zeta23_Assembly_eps_form_twoThirds

-- from Zeta23.Main
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Main.lean — ζ-level headline theorems: proofs.
Instantiates the abstract §6 assembly (Zeta23.Assembly, over an arbitrary ZeroConfig) at the
nontrivial zeros of Mathlib's riemannZeta (Zeta23.zetaZeros), and performs the λ → 1⁻ and
dyadic-summation wrappers. See Zeta23/Statement.lean for the definitions being talked about.
-/

open Filter Topology

noncomputable section

namespace Zeta23

section wrappers
variable (hs : ZetaSeam)












end wrappers

/-! ## Theorem A from PaperInputs + the thm:traces hypothesis

`thmA_of_traces` is a named declaration whose type shows exactly what is assumed: the
published inputs H : PaperInputs, a taper profile, and the thm:traces hypothesis
ThmTracesHyp (stated on the prime-side ν_X integrals). The zero-side block package and the
tail package are discharged from the sibling files. -/

section M1

open Assembly








end M1

section M1BC

open Assembly



variable (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 → ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig)
include H hϱ hTr





end M1BC

/-! ## Minimal trust base, displayed in the type

The literature-form explicit formula EF_lit ([eq:EFstd]) implies the paper form given
H-Γ (Zeta23.EF.explicitFormulaPaper_of_lit), and H-cheb is a theorem (Zeta23.Cheb.chebyshevMertens).
So the published inputs reduce to: EF_lit, Riemann–von Mangoldt (+ local count),
Montgomery–Vaughan, and the Γ-facts. -/

section TrustBase



end TrustBase

section M1Std




end M1Std

end Zeta23
end
open Filter Topology
open Zeta23
variable (hs : ZetaSeam)

theorem solution
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  Assembly.eps_form_twoThirds (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0star T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _) h
