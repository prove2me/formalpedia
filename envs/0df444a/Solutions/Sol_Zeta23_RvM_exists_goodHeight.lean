-- Prove2me | solution 1 for Zeta23.RvM.exists_goodHeight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:54:00.730296+00:00
-- url     : https://prove2.me/submissions/48950306-a634-4ab3-85d9-f9f1697f7b79

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

-- from Zeta23.Defs.Counting
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs/Counting.lean — elementary counting facts for an abstract ZeroConfig.
[eq:trivialchain] at the abstract level; Statement.lean transfers it to ζ.
-/

open Set

noncomputable section

namespace Zeta23.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

lemma window_finite : (Z.window T₁ T₂).Finite := Z.finite_window T₁ T₂








end Zeta23.ZeroConfig
end
end

-- from Zeta23.Statement
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement.lean — the statement layer.

Canonical text: the paper, §1 [Results], [eq:trivialchain], [thm:A], [thm:B], [thm:C].

It (1) defines nontrivial zeros, multiplicity (via analyticOrderAt) and the six counting functions of
§1 directly against Mathlib; (2) packages the "seam" facts needed to view them as an abstract
Zeta23.ZeroConfig (structure ZetaSeam — classical facts about ζ, established from Mathlib elsewhere in
the repository, not paper inputs); (3) states Theorems A, B, C in ε-form (fixed λ ∈ (0,1) with
constant H(λ), F(λ), then the 2/3, 1/2, 3/4 liminf wrappers via λ → 1⁻);
(4) proves the sanity anchors connecting to Mathlib's RiemannHypothesis and [eq:trivialchain].
-/

open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

namespace Zeta23

/-! ## 1. Nontrivial zeros and multiplicity, against Mathlib -/










/-! ## 2. The seam: ζ's zeros as an abstract ZeroConfig -/



section seam_rfl
variable (hs : ZetaSeam) (T₁ T₂ : ℝ)

@[simp] lemma zetaZeros_carrier : (zetaZeros hs).carrier = {ρ | IsNontrivialZero ρ} := rfl
@[simp] lemma zetaZeros_mult : (zetaZeros hs).mult = zeroMult := rfl
@[simp] lemma zetaZeros_simple : (zetaZeros hs).simple = {ρ | zeroMult ρ = 1} := rfl

lemma zetaZeros_window : (zetaZeros hs).window T₁ T₂ = zerosIn T₁ T₂ := by
  ext ρ; simp [ZeroConfig.window, zerosIn]

@[simp] lemma zetaZeros_N : (zetaZeros hs).N T₁ T₂ = Ncount T₁ T₂ := by
  simp [ZeroConfig.N, Ncount, zetaZeros_window]
@[simp] lemma zetaZeros_Nd : (zetaZeros hs).Nd T₁ T₂ = Ndist T₁ T₂ := by
  simp [ZeroConfig.Nd, Ndist, zetaZeros_window]
@[simp] lemma zetaZeros_N0 : (zetaZeros hs).N0 T₁ T₂ = N0 T₁ T₂ := by
  simp [ZeroConfig.N0, N0, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0star : (zetaZeros hs).N0star T₁ T₂ = N0star T₁ T₂ := by
  simp [ZeroConfig.N0star, N0star, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0s : (zetaZeros hs).N0s T₁ T₂ = N0simple T₁ T₂ := by
  simp [ZeroConfig.N0s, N0simple, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_Ns : (zetaZeros hs).Ns T₁ T₂ = Nsimple T₁ T₂ := by
  simp [ZeroConfig.Ns, Nsimple, zetaZeros_window]

end seam_rfl

/-! ## 3. Sanity anchors (connection to Mathlib's existing statement of RH) -/





/-! ## 4. Theorems A, B, C

The headline theorems Zeta23.thmA, thmA_cumulative, thmA_lam, thmB, thmB_cumulative, thmB_lam, thmC,
thmC_cumulative, thmC_lam are proved in Zeta23/Final.lean (their types display the full trust base:
literature explicit formula, Riemann–von Mangoldt, Montgomery–Vaughan, Γ-facts), on top of the
versions Zeta23.thmA_of_traces etc. in Zeta23/Main.lean (thm:traces as an explicit hypothesis). This file
stays light (definitions + anchors) so that it can be read and imported cheaply.

Paper [thm:A], verbatim: "Let 0 < λ ≤ 1 be fixed. There are constants c(λ) > 0 and T₀(λ) such that
for all T ≥ T₀(λ)   N₀*(T,2T) ≥ (H(λ) − c(λ) loglogT/logT) N(T,2T),
and for λ < 1 the factor loglog T may be omitted. In particular
  liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3,   liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3".
Formal target: the ε-forms, for each fixed λ ∈ (0,1) with constant
H(λ) (resp. 2F(λ)−1, F(λ)), which absorb c(λ)/log T; then the 2/3 (resp. 1/2, 3/4) forms via
sup_{λ<1} H(λ) = H(1) = 2/3 etc. The effective c(λ) forms are not stated. -/




end Zeta23
end
end

-- from Zeta23.Statement.SeamClosed
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement/SeamClosed.lean — the ζ-seam is closed.
All four fields of Zeta23.ZetaSeam are theorems of Mathlib:
  one_le_mult, finite_window  — Zeta23/Statement/Seam.lean ;
  reflect_zero, mult_reflect  — Zeta23/ZetaReflect.lean (Schwarz reflection
                                 riemannZeta_conj + functional equation at the analyticOrderAt level).
Hence the abstract ZeroConfig of ζ's nontrivial zeros and [eq:trivialchain] are hypothesis-free.
-/

noncomputable section

namespace Zeta23



@[simp] lemma zetaZeroConfig_carrier : zetaZeroConfig.carrier = {ρ | IsNontrivialZero ρ} := rfl
@[simp] lemma zetaZeroConfig_mult : zetaZeroConfig.mult = zeroMult := rfl

@[simp] lemma zetaZeroConfig_N (T₁ T₂ : ℝ) : zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N _ _ _
@[simp] lemma zetaZeroConfig_N0star (T₁ T₂ : ℝ) : zetaZeroConfig.N0star T₁ T₂ = N0star T₁ T₂ :=
  zetaZeros_N0star _ _ _
@[simp] lemma zetaZeroConfig_N0s (T₁ T₂ : ℝ) : zetaZeroConfig.N0s T₁ T₂ = N0simple T₁ T₂ :=
  zetaZeros_N0s _ _ _
@[simp] lemma zetaZeroConfig_Nd (T₁ T₂ : ℝ) : zetaZeroConfig.Nd T₁ T₂ = Ndist T₁ T₂ :=
  zetaZeros_Nd _ _ _


/-- Finiteness of every ordinate window of nontrivial zeros, hypothesis-free. -/
theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite := by
  simpa [zetaZeros_window] using (zetaZeros zetaSeam).window_finite T₁ T₂

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

theorem solution (a : ℝ) : ∃ T ∈ Set.Icc a (a + 1), GoodHeight T := by
  have hfin : ((fun ρ : ℂ => ρ.im) '' zerosIn a (a + 1)).Finite :=
    (zerosIn_finite a (a + 1)).image _
  have hinf : (Set.Ioo a (a + 1)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨T, hT⟩ := (hinf.diff hfin).nonempty
  obtain ⟨hT, hTnot⟩ := hT
  refine ⟨T, ⟨hT.1.le, hT.2.le⟩, ?_⟩
  intro ρ hρ him
  apply hTnot
  refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
  · rw [him]; exact hT.1
  · rw [him]; exact hT.2.le
