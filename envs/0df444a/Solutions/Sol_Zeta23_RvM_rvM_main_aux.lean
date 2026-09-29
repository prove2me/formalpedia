-- Prove2me | solution 1 for Zeta23.RvM.rvM_main_aux
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:24:02.305569+00:00
-- url     : https://prove2.me/submissions/991138a9-335f-44ee-822e-f148d776c28c

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
import Mathlib.Analysis.Calculus.LogDeriv
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
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
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_RvM_GammaSide
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_RvM_ReZeroCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_RvM_mu_le_log
import Theorems.Thm_Zeta23_RvM_rvM_main_param
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count

-- from Zeta23.RvM.GammaSide
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/GammaSide.lean — the Γ-factor side of the folded contour is
EXACTLY the paper's ∫μ:  (1/π)·Im ∫_L Γℝ'/Γℝ ds = ∫_{T₁}^{T₂} μ(t) dt  for 0 < T₁,
because Γℝ'/Γℝ is holomorphic on Re s > 0 (Cauchy–Goursat on [½,2]×[T₁,T₂] moves L to the critical-line
segment) and Re Γℝ'/Γℝ(½+it) = ½ Re ψ(¼+it/2) − ½ log π = π·μ(t)  (Γℝ(s) = π^{−s/2}Γ(s/2), μ = Zeta23.mu).
-/

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

namespace Zeta23.RvM










/-! ### helpers for the assembly -/

/-- μ is continuous (given H-Γ's smoothness field). -/
theorem mu_continuous (hΓ : Zeta23.GammaFacts) : Continuous mu :=
  hΓ.smooth.continuous


end Zeta23.RvM
end
end

-- from Zeta23.RvM.MainTerm
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/MainTerm.lean — the main term N(T,2T) = (T/2π)·ell1 T + O(log T).
The statements here are assembled into Zeta23.RvM.riemannVonMangoldt in Zeta23/RvM/Statement.lean.

Inputs (from other files):
 * Zeta23.RvM.zetaZeroConfig_local_count (LocalCount.lean, proved): local count.
 * Zeta23/Analytic/RectangleLogDeriv.lean: ∮_{∂Rect} g·f'/f = 2πi Σ m_ρ g(ρ) (PNT+ RectangleIntegral'
   conventions) — use with g ≡ 1, f = completedRiemannZeta (or riemannZeta·Gammaℝ) on [−1,2]×[T₁,T₂]
   (mind Λ's poles at s = 0, 1: for T₁ > 0 the rectangle avoids them).
 * Zeta23/WeilEF/XiLogDeriv.lean: logDeriv Λ = logDeriv ζ + logDeriv Gammaℝ (Re s > 0, away from
   zeros/pole); conj-symmetry Λ(conj s) = conj Λ(s); Λ(1−s) = Λ(s) (Mathlib completedRiemannZeta_one_sub).
 * Zeta23/RvM/Backlund.lean: backlund_horizontal (∃ C T₀, ∀ T ≥ T₀, GoodHeight T →
   |Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ C log T) and vertical_two (|Im ∫_{T₁}^{T₂} ζ'/ζ(2+it)·i dt| ≤ 2 log 3).
 * Zeta23/RvM/GammaSide.lean: gamma_side : 0 < T₁ ≤ T₂ → (1/π)·(halfContour (logDeriv Gammaℝ) T₁ T₂).im
   = ∫ t in T₁..T₂, mu t.
 * GammaFacts.int_mu, GammaFacts.stirling (μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²) ⇒ μ ≪ log on [T−1,2T+1]).
The assembly is proved once as the constant-parametric `rvM_main_param`; `rvM_main_aux` /
`rvM_main` are its ∃-corollaries; MainTermExplicit.lean keeps only the numeric inputs and `rvM_main_explicit`.
-/

open Complex MeasureTheory

attribute [-instance] LieAlgebra.ofAssociativeAlgebra

noncomputable section

namespace Zeta23.RvM









/-! (window arithmetic Ncount_add / Ncount_mono: Zeta23/Statement/SeamClosed.lean) -/




end Zeta23.RvM
end
open Complex MeasureTheory
open Zeta23
open Zeta23.RvM

theorem solution (hΓ : GammaFacts)
    (backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T)
    (vertical_two : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T := by
  obtain ⟨CB, TB, hB⟩ := backlund_horizontal
  obtain ⟨A₀, hA₀1, hA₀⟩ := zeta_local_zero_count
  obtain ⟨Cμ, Tμ, hCμ⟩ := hΓ.int_mu
  obtain ⟨CM, hCM0, hCM⟩ := mu_le_log hΓ
  exact ⟨_, _, rvM_main_param hB vertical_two hA₀1 hA₀ hCμ hCM0 hCM (mu_continuous hΓ)⟩
