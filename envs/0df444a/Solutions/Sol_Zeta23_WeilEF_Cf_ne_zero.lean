-- Prove2me | solution 1 for Zeta23.WeilEF.Cf_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:45:43.144667+00:00
-- url     : https://prove2.me/submissions/1157977a-1b07-475f-8dc1-e6bcb781c6a5

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
import Theorems.Thm_ZeroFactorization

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

theorem solution {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ ≤ r) : Cf r f z ≠ 0 := by
  have hfinr := finiteSetOfZeros_mono hr1 hfin
  by_cases hmem : z ∈ SetOfZeros r f
  · -- regularized value: ZeroFactor f z ≠ 0 over a nonvanishing finite product
    obtain ⟨h_ρ, _, hρ0, hZF, _⟩ := ZeroFactorization hr1 hfa hf0 hmem
    unfold Cf
    rw [dif_pos hfinr, dif_pos hmem, hZF]
    apply div_ne_zero hρ0
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
    have hne : z ≠ ρ := by
      intro h
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hρ
      exact hρ.2 h.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)
  · unfold Cf
    rw [dif_pos hfinr, dif_neg hmem]
    have hfz : f z ≠ 0 := by
      intro h
      exact hmem ⟨hz, h⟩
    apply div_ne_zero hfz
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
    have hρ' := hfinr.mem_toFinset.mp hρ
    have hne : z ≠ ρ := by
      rintro rfl
      exact hmem hρ'
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)
