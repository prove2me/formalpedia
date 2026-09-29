-- Prove2me | solution 1 for Zeta23.RvM.rvM_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:21:51.698763+00:00
-- url     : https://prove2.me/submissions/bc5a2260-94ef-4aa8-a967-39519c2a9f12

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
import Theorems.Thm_Zeta23_RvM_backlund_horizontal_of_count
import Theorems.Thm_Zeta23_RvM_reZeroSet_card_le_of_growth
import Theorems.Thm_Zeta23_RvM_rvM_main_aux
import Theorems.Thm_Zeta23_RvM_vertical_two
import Theorems.Thm_Zeta23_RvM_zeta_growth_right_at

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


/-! ## The half-plane bound  [Tit86, (2.1.4) with N = 1] -/


/-! ## Linear growth in σ ≥ δ  [Tit86, §5.1] -/





theorem zeta_growth_right :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A :=
  ⟨1, 20 / 3, by norm_num, zeta_growth_right_at⟩

/-! ## Bounds on Re s ≥ 2 (the Jensen disc centre)  -/









end RvM
end Zeta23
end
end

-- from Zeta23.RvM.ReZeroCount
section
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







/-- **(J) the Jensen half of Backlund's bound**: #{σ ∈ [1/2,2] : Re ζ(σ+iT) = 0} ≪ log T. -/
theorem reZeroSet_card_le : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T := by
  obtain ⟨A, C, hC, hgrowth⟩ := zeta_growth_right
  exact ⟨_, 4, reZeroSet_card_le_of_growth hC hgrowth⟩


end Zeta23.RvM
end
end

-- from Zeta23.RvM.Backlund
section
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




/-- **Backlund's bound**. For all large T that are not ordinates of nontrivial zeros,
|Im ∫_{1/2}^{2} ζ'/ζ(σ + iT) dσ| ≤ C·log T. -/
theorem backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T :=
  backlund_horizontal_of_count reZeroSet_card_le


/-! ## The vertical side σ = 2 -/






end RvM
end Zeta23
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
set_option maxHeartbeats 1000000

theorem solution (hΓ : GammaFacts) : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T :=
  rvM_main_aux hΓ backlund_horizontal vertical_two
