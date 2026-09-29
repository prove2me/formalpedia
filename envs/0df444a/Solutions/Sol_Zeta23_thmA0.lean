-- Prove2me | solution 1 for Zeta23.thmA0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:48:27.115307+00:00
-- url     : https://prove2.me/submissions/1ca062e6-d54c-4346-a4fd-ea6ffb09b9a6

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Defs_Profile
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_GammaFacts_IntMu
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_MV
import Definitions.Def_Zeta23_MV_Duality
import Definitions.Def_Zeta23_MV_Quadratic
import Definitions.Def_Zeta23_MV_Spacing
import Definitions.Def_Zeta23_Main
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsE1
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Definitions.Def_Zeta23_PrimeSideB
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideB_PP
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Definitions.Def_Zeta23_PrimeSideB_Traces
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_RvM_BacklundDefs
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_RvM_GammaSide
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_RvM_ReZeroCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Definitions.Def_Zeta23_Taper_Basic
import Definitions.Def_Zeta23_Taper_Params
import Definitions.Def_Zeta23_TracesBoundsE
import Definitions.Def_Zeta23_WeilEF_FullLine
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Definitions.Def_Zeta23_WeilEF_ZeroSummability
import Definitions.Def_Zeta23_ZeroSide
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_WeilEF_EF_lit_zeta
import Theorems.Thm_Zeta23_thmA1

-- from Zeta23.WeilEF.Main
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Main.lean — Final assembly: EF_lit for the concrete ζ zero configuration.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex MeasureTheory
open scoped ArithmeticFunction




/-- **Hypothesis-free form**: [eq:EFstd] holds for the canonical
unconditional ζ zero configuration. -/
theorem EF_lit_zetaZeroConfig : Zeta23.EF.EF_lit zetaZeroConfig := EF_lit_zeta zetaSeam

end WeilEF
end Zeta23
end
end

-- from Zeta23.Final
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Final.lean — the headline theorems.

  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line",
   Theorems A, B, C — ε-forms.

Each theorem's TYPE in the first section displays the inputs as separate named hypotheses:
  hEF  : EF.EF_lit zetaZeroConfig        — Weil's explicit formula, literature form [eq:EFstd]
                                           ([IK04, Thm 5.12] for ζ), over ζ's nontrivial zeros;
  hRvM : RiemannVonMangoldt zetaZeroConfig — [eq:RvM] + local count N(t+1)−N(t) ≤ A₀ log(|t|+3);
  hMV  : ∃ C > 0, MVDiag C                — Montgomery–Vaughan weighted Hilbert inequality, literature
                                           (y = x) form [MV74, Thm 2]; the paper's bilinear [lem:MV] is
                                           derived (Zeta23.MVHilbert_of_diag);
  hΓ   : GammaFacts                        — Stirling-type facts for μ [eq:mufacts], [eq:muints].
Nothing else: the Chebyshev–Mertens bounds [lem:cheb] are proved (Zeta23.Cheb.chebyshevMertens), the
paper's spectral form of the explicit formula [eq:EF] is derived from hEF (Zeta23.EF), the taper profile
is Mathlib's Real.smoothTransition (Zeta23.stdProfile), the ζ-facts (analytic order, functional-equation
symmetry, local finiteness) are proved (Zeta23.zetaSeam), and thm:traces [thm:traces] is
Zeta23.PrimeSide.thm_traces (the versions with thm:traces as an explicit hypothesis are
Zeta23.thmA_of_traces etc. in Zeta23/Main.lean). Later sections discharge the hypotheses
hMV, hΓ, hRvM and hEF one by one, ending with the unconditional forms.

Counting functions (Zeta23/Statement.lean): Ncount T₁ T₂ = N(T₁,T₂) with multiplicity (analytic order of
riemannZeta), N0star = N₀* (on the line, distinct), N0simple = N₀ˢ (on the line, simple), Ndist = N_d
(distinct), all over nontrivial zeros ρ (ζ ρ = 0, 0 < Re ρ < 1) with T₁ < Im ρ ≤ T₂.
-/

open Filter

noncomputable section

namespace Zeta23

section Final


variable (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
  (hMV : ∃ C : ℝ, 0 < C ∧ MVDiag C) (hΓ : GammaFacts)
include hEF hRvM hMV hΓ











end Final

/-! ## Three-hypothesis forms: H-MV is a theorem (Zeta23.MV.mv_hilbert — the weighted Hilbert
inequality of Montgomery–Vaughan 1974, proved outright). -/

section ThreeHyp


variable (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig) (hΓ : GammaFacts)
include hEF hRvM hΓ







end ThreeHyp

/-! ## Two-hypothesis forms: H-Γ is a theorem (Zeta23.gammaFacts; proved via
digamma partial fractions + vertical Stirling + FTC). -/

section TwoHyp


variable (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig)
include hEF hRvM







end TwoHyp

/-! ## One-hypothesis forms: H-RvM is a theorem given the proved Γ-facts
(local count + folded argument principle + Backlund; Zeta23/RvM/*). -/

section OneHyp



variable (hEF : EF.EF_lit zetaZeroConfig)
include hEF







end OneHyp

/-! ## Unconditional forms: the explicit formula is a theorem
(Zeta23.WeilEF.EF_lit_zetaZeroConfig — Weil/Riemann–von Mangoldt explicit formula for ζ,
literature form [eq:EFstd], proved from Mathlib's functional equation by contour integration).
These are the headline statements of the formalization: no hypotheses at all. -/

section Unconditional

/-- **Weil's explicit formula for ζ**, re-exported. -/
theorem zetaEF : EF.EF_lit zetaZeroConfig := WeilEF.EF_lit_zetaZeroConfig








end Unconditional

section AFortiori



end AFortiori

section UnconditionalAFortiori



end UnconditionalAFortiori


end Zeta23
end
open Filter
open Zeta23

theorem solution :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA1 zetaEF
