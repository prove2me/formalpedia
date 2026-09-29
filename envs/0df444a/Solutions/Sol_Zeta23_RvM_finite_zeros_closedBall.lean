-- Prove2me | solution 1 for Zeta23.RvM.finite_zeros_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:53:06.294645+00:00
-- url     : https://prove2.me/submissions/addc7f96-3341-4953-99c6-76acd6a99734

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

-- from Zeta23.RvM.ReZeroCount
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ReZeroCount.lean — the Jensen half (J) of Backlund's bound:
the number of zeros of Re ζ(σ + iT) on σ ∈ [1/2, 2] is ≪ log T.
Route: g(z) := (ζ(z+iT) + ζ(z−iT))/2 is analytic away from 1 ± iT and equals Re ζ(σ+iT) for real σ
(riemannZeta_conj); g(2) = Re ζ(2+iT) ≥ 2 − π²/6 > 1/3; rescale |z−2| ≤ 1.9 to the unit disc and
apply the ported PNT+ ZerosBound (r = 0.8, R = 0.9) with zeta_growth_right on both summands.
Used by Zeta23/RvM/Backlund.lean for backlund_horizontal.
-/

open Complex Set Metric

noncomputable section

namespace Zeta23.RvM









end Zeta23.RvM
end
open Complex Set Metric
open Zeta23
open Zeta23.RvM

theorem solution {f : ℂ → ℂ} {R r : ℝ} (hrR : r < R)
    (hA : AnalyticOnNhd ℂ f (Metric.ball 0 R)) {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball 0 R)
    (hfz₀ : f z₀ ≠ 0) : {z : ℂ | ‖z‖ ≤ r ∧ f z = 0}.Finite := by
  have hU : IsPreconnected (Metric.ball (0:ℂ) R) := (convex_ball 0 R).isPreconnected
  rcases hA.eqOn_zero_or_eventually_ne_zero_of_preconnected hU with h0 | hcod
  · exact absurd (h0 hz₀) hfz₀
  rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
  have hsub : Metric.closedBall (0:ℂ) r ⊆ Metric.ball 0 R := Metric.closedBall_subset_ball hrR
  -- choose, for every z in the closed ball, a neighbourhood with finitely many zeros
  have hloc : ∀ z ∈ Metric.closedBall (0:ℂ) r, ∃ t ∈ nhds z,
      (t ∩ {x : ℂ | x ∈ Metric.ball (0:ℂ) R ∧ f x = 0}).Finite := by
    intro z hz
    obtain ⟨t, ht, hfin⟩ := hcod z (hsub hz)
    refine ⟨t, ht, hfin.subset ?_⟩
    rintro x ⟨hxt, hxU, hx0⟩
    exact ⟨hxt, hxU, by simpa using hx0⟩
  choose t ht hfin using hloc
  obtain ⟨I, hcover⟩ := (isCompact_closedBall (0:ℂ) r).elim_nhds_subcover' t ht
  refine ((I.finite_toSet.biUnion fun z _ => hfin z z.2).subset ?_)
  rintro x ⟨hxr, hx0⟩
  have hxball : x ∈ Metric.closedBall (0:ℂ) r := by
    rwa [Metric.mem_closedBall, _root_.dist_zero_right]
  obtain ⟨z, hzI, hxz⟩ := Set.mem_iUnion₂.mp (hcover hxball)
  exact Set.mem_iUnion₂.mpr ⟨z, hzI, hxz, hsub hxball, hx0⟩
