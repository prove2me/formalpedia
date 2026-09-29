-- Prove2me | solution 1 for Zeta23.RvM.backlund_horizontal_of_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:55:50.355735+00:00
-- url     : https://prove2.me/submissions/1a2bf235-92ee-4c57-ae5a-67863a95b783

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_BacklundDefs
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_RvM_ReZeroCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect
import Theorems.Thm_Zeta23_RvM_backlund_horizontal_of_count_at

-- from Zeta23.RvM.Backlund
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Backlund.lean — Backlund's bound for the horizontal variation of arg ζ, and the trivial
vertical side σ = 2. Consumed by Zeta23/RvM/Statement.lean, which proves
  N(T₁,T₂) = ∫_{T₁}^{T₂} μ + (1/π)·Im ∫_L ζ'/ζ ds,  L = ½+iT₁ → 2+iT₁ → 2+iT₂ → ½+iT₂
for non-ordinate heights and assembles RvM.main from GammaFacts.int_mu + the two bounds below.

* `backlund_horizontal` [Tit86 §9.4, Backlund 1918]: for T large and not the ordinate of a zero,
    |Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ C log T.
  Route: g(z) := (ζ(z+iT) + conj ζ(z̄+iT))/2 is analytic near the disc |z−2| ≤ 1.9 and equals
  Re ζ(σ+iT) for real σ; g(2) = Re ζ(2+iT) ≥ 2 − π²/6 > 0; ZerosBound (PNT+ port, unit disc,
  r = 0.8, R = 0.9 after scaling by 1.9) + Zeta23.RvM.zeta_growth (δ = 0.2) give
  #{σ ∈ [½,2] : Re ζ(σ+iT) = 0} ≤ C log T; on each of the ≤ m+1 subintervals where Re ζ(σ+iT)
  has constant sign, Complex.log ∘ (±ζ(·+iT)) is a primitive of ζ'/ζ with |Im| ≤ π.
* `vertical_two`: |Im (I·∫_{T₁}^{T₂} ζ'/ζ(2+it) dt)| ≤ π — log ζ is a primitive on σ ≥ 2
  (‖ζ − 1‖ ≤ π²/6 − 1 < 1 there, Zeta23.RvM.norm_riemannZeta_sub_one_le), and
  |arg ζ(2+it)| ≤ π/2 since Re ζ(2+it) > 0.
-/

open Complex Set MeasureTheory Real intervalIntegral

/- INSTANCE HYGIENE: `Zeta23.FromPNTPlus.StrongPNTPrefix` transitively imports
`Mathlib.Algebra.Lie.OfAssociative`, whose instance `LieAlgebra.ofAssociativeAlgebra` offers a second
(non-reducibly-defeq) route to `Module ℝ ℂ`; combined with this file's other imports that makes
`ContinuousSMul ℝ ℂ` — hence every `HasDerivAt (f : ℝ → ℂ)` — fail to synthesize (diagnosed
with `trace.Meta.synthInstance`).  Lie algebras are never used here. -/
attribute [-instance] LieAlgebra.ofAssociativeAlgebra

noncomputable section

namespace Zeta23
namespace RvM


/-! ## The horizontal side, calculus half: variation of the argument

Fix a height `T ≠ 0` with `ζ ≠ 0` on the segment `[1/2, 2] + iT`.  If `Re ζ(σ+iT)` has no zero on an
open subinterval `(u,v)`, it has constant sign `ε` there (IVT), `log(ε ζ(σ+iT))` is a primitive of
`ζ'/ζ(σ+iT)` on `[u,v]` (at the endpoints `ε ζ` is `≥ 0` in real part and `≠ 0`, so still in the
slit plane), hence `|Im ∫_u^v ζ'/ζ| ≤ 2π`.  Splitting `[1/2,2]` at the finitely many zeros of
`Re ζ(σ+iT)` (the set `reZeroSet T`, counted by the Jensen bound `reZeroSet_card_le`) gives
`|Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ 2π (#reZeroSet T + 1)` — by induction on the number of zeros inside
the interval (no sorting needed). -/

section Variation

variable {T : ℝ}










end Variation

/-! ## Assembly of Backlund's bound from (J) = `reZeroSet_card_le`  and (V) -/






/-! ## The vertical side σ = 2 -/






end RvM
end Zeta23
end
open Complex Set MeasureTheory Real intervalIntegral
open Zeta23
open RvM

theorem solution
    (hJ : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T := by
  obtain ⟨C, T₀, hJ⟩ := hJ
  exact ⟨_, _, backlund_horizontal_of_count_at hJ⟩
