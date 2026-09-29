-- Prove2me | solution 1 for Zeta23.RvM.vertical_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:22:56.82234+00:00
-- url     : https://prove2.me/submissions/b5d6ec33-2d33-4559-9000-d5cfd25bec57

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
import Theorems.Thm_Zeta23_RvM_hasDerivAt_log_riemannZeta_two
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le

-- from Zeta23.RvM.ZetaGrowth
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta23_Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/

open Complex Set MeasureTheory Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Analyticity away from the pole -/

/-- ζ is analytic on a neighbourhood of every set not containing 1. -/
theorem analyticOnNhd_riemannZeta {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ riemannZeta S := by
  have h : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  exact h.mono (Set.subset_compl_singleton_iff.mpr hS)

/-! ## The half-plane bound  [Tit86, (2.1.4) with N = 1] -/


/-! ## Linear growth in σ ≥ δ  [Tit86, §5.1] -/






/-! ## Bounds on Re s ≥ 2 (the Jensen disc centre)  -/


/-- π²/6 − 1 < 1 (π < 3.15 ⇒ π² < 9.93 < 12). -/
lemma pi_sq_div_six_sub_one_lt_one : Real.pi ^ 2 / 6 - 1 < 1 := by
  have := Real.pi_lt_d2  -- π < 3.15
  nlinarith [Real.pi_pos]







end RvM
end Zeta23
end
end

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

/-- `Re ζ(2+it) > 0` (indeed `≥ 2 − π²/6`), from `‖ζ(s) − 1‖ ≤ π²/6 − 1 < 1` on `Re s ≥ 2`. -/
lemma re_riemannZeta_two_pos (t : ℝ) : 0 < (riemannZeta (2 + t * I)).re := by
  have h := norm_riemannZeta_sub_one_le (s := 2 + t * I) (by simp)
  have h2 : |(riemannZeta (2 + t * I) - 1).re| ≤ ‖riemannZeta (2 + t * I) - 1‖ :=
    Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.one_re] at h2
  have h3 := (abs_le.mp (h2.trans h)).1
  linarith [pi_sq_div_six_sub_one_lt_one]

lemma two_add_mul_I_ne_one (t : ℝ) : (2 : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this


/-- Continuity of `t ↦ ζ'/ζ(2+it)·i`. -/
lemma continuous_logDeriv_riemannZeta_two :
    Continuous (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I) := by
  have hγ : Continuous (fun t : ℝ => (2 : ℂ) + t * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  have hd : Continuous (fun t : ℝ => deriv riemannZeta (2 + t * I)) :=
    hA.deriv.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hz : Continuous (fun t : ℝ => riemannZeta (2 + t * I)) :=
    hA.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hne : ∀ t : ℝ, riemannZeta (2 + t * I) ≠ 0 := fun t h => by
    have := re_riemannZeta_two_pos t; rw [h] at this; simp at this
  simp only [logDeriv_apply]
  exact ((hd.div hz hne).mul continuous_const)


end RvM
end Zeta23
end
open Complex Set MeasureTheory Real intervalIntegral
open Zeta23
open RvM

theorem solution : ∀ T₁ T₂ : ℝ,
    |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi := by
  intro T₁ T₂
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_log_riemannZeta_two t)
    (continuous_logDeriv_riemannZeta_two.intervalIntegrable _ _)]
  rw [Complex.sub_im, Complex.log_im, Complex.log_im]
  have h1 : |(riemannZeta (2 + T₂ * I)).arg| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (re_riemannZeta_two_pos T₂).le
  have h2 : |(riemannZeta (2 + T₁ * I)).arg| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (re_riemannZeta_two_pos T₁).le
  calc |(riemannZeta (2 + T₂ * I)).arg - (riemannZeta (2 + T₁ * I)).arg|
      ≤ |(riemannZeta (2 + T₂ * I)).arg| + |(riemannZeta (2 + T₁ * I)).arg| := abs_sub _ _
    _ ≤ π / 2 + π / 2 := add_le_add h1 h2
    _ = π := by ring
