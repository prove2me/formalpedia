-- Prove2me | solution 1 for Zeta23.WeilEF.finite_SetOfZeros
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:32:32.957954+00:00
-- url     : https://prove2.me/submissions/226ecf54-f9a4-4008-8c4b-39e7097fdc73

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
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
import Definitions.Def_Zeta23_Statement

-- from Zeta23.WeilEF.Landau
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Landau.lean

Landau's lemma (Borel–Carathéodory + Jensen route; Mathlib: Analysis/Complex/BorelCaratheodory,
JensenFormula): zero counts and the partial-fraction expansion of f'/f on disks, specialized to ζ.
`zeta_local_zero_count` is consumed downstream as `RiemannVonMangoldt.local_count`.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set


section UnitDisk

open Metric










end UnitDisk



end WeilEF
end Zeta23
end
open Zeta23
open Complex Set
open Metric

theorem solution {f : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 ≠ 0) :
    (SetOfZeros 1 f).Finite := by
  set U := Metric.closedBall (0 : ℂ) 1 with hU
  have h0U : (0 : ℂ) ∈ U := by
    rw [hU, Metric.mem_closedBall, dist_self]
    norm_num
  have hcod : {z : ℂ | f z ≠ 0} ∈ Filter.codiscreteWithin U := by
    rcases hfa.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (by rw [hU]; exact Metric.isPreconnected_closedBall) with h | h
    · exact absurd (h h0U) hf0
    · exact h
  rw [codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
  have hsub1 : Metric.closedBall (0 : ℂ) 1 ⊆ U := subset_rfl
  choose t ht htfin using fun z (hz : z ∈ Metric.closedBall (0:ℂ) 1) => hcod z (hsub1 hz)
  obtain ⟨s, hs⟩ := (isCompact_closedBall (0:ℂ) 1).elim_nhds_subcover'
    (fun z hz => t z hz) (fun z hz => ht z hz)
  refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet
    (fun z _ => htfin z.1 z.2)) ?_
  intro ρ hρ
  have hρball : ρ ∈ Metric.closedBall (0:ℂ) 1 := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    exact hρ.1
  obtain ⟨z, hz, hρz⟩ := Set.mem_iUnion₂.mp (hs hρball)
  refine Set.mem_biUnion hz ?_
  refine ⟨hρz, hsub1 hρball, ?_⟩
  simp only [Set.mem_setOf_eq, not_not]
  exact hρ.2
