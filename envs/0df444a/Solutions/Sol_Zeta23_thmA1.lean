-- Prove2me | solution 1 for Zeta23.thmA1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:50:04.915881+00:00
-- url     : https://prove2.me/submissions/db7f2585-8694-4ecb-873f-7920c7c831d8

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
import Theorems.Thm_Zeta23_MuFields_mu_deriv_bound
import Theorems.Thm_Zeta23_MuFields_mu_monotoneOn
import Theorems.Thm_Zeta23_MuFields_mu_zero_le
import Theorems.Thm_Zeta23_MuFields_neg_one_lt_mu_zero
import Theorems.Thm_Zeta23_MuInts_int_mu_of_stirling
import Theorems.Thm_Zeta23_MuInts_int_mu_sq_of_stirling
import Theorems.Thm_Zeta23_RvM_rvM_main
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Theorems.Thm_Zeta23_StirlingVert_mu_stirling
import Theorems.Thm_Zeta23_mu_even
import Theorems.Thm_Zeta23_mu_smooth
import Theorems.Thm_Zeta23_thmA3

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



end Zeta23
end
end

-- from Zeta23.GammaFacts.Complete
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Complete.lean — assembly of H-Γ:
All nine fields of Zeta23.GammaFacts ([eq:mufacts] + the Γ-halves of [eq:muints])
are proved: even/smooth (Zeta23/GammaFacts.lean), monotoneOn/mu_zero_le/
neg_one_lt_mu_zero/deriv_bound (Zeta23/GammaFacts/Mu.lean, via the digamma
partial-fraction series), stirling (Zeta23/GammaFacts/StirlingVert.lean, C = 20/2π),
int_mu/int_mu_sq (Zeta23/GammaFacts/IntMu.lean, from stirling + FTC).
-/

noncomputable section

namespace Zeta23

/-- GammaFacts from any Stirling bound for μ (the only analytically deep field). -/
theorem gammaFacts_of_stirling (hst : MuInts.StirlingHyp) : GammaFacts :=
  ⟨mu_even, mu_smooth, MuFields.mu_monotoneOn, MuFields.mu_zero_le, MuFields.neg_one_lt_mu_zero,
    hst, MuFields.mu_deriv_bound, MuInts.int_mu_of_stirling hst, MuInts.int_mu_sq_of_stirling hst⟩

/-- **H-Γ, unconditionally.** -/
theorem gammaFacts : GammaFacts := gammaFacts_of_stirling StirlingVert.mu_stirling

end Zeta23
end
end

-- from Zeta23.RvM.LocalCount
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/LocalCount.lean

H-RvM's local count for Mathlib's ζ:  N(t, t+1] ≤ A₀ log(|t| + 3) for all real t
(= Zeta23.RiemannVonMangoldt.local_count at Z := zetaZeroConfig; [Tit86, Thm 9.2]).

Route (never evaluating ζ left of σ = 0.19, so no Stirling is needed):
 * count only zeros with β ≥ 1/2 and double (Zeta23.ZeroConfig.N_le_two_mul_half, Zeta23/RvM/Halving.lean,
   via the ρ ↦ 1−ρ̄ symmetry);
 * Jensen-type zero count on a disc: the ported PNT+ `ZerosBound` (Zeta23/FromPNTPlus/StrongPNTPrefix.lean,
   Apache-2.0) applied to g(w) := ζ(c₀ + 1.9 w)/ζ(c₀), c₀ := 2 + (t+½)i, r = 0.84, R = 0.95:
   the β ≥ 1/2 part of the window lies in ‖w‖ ≤ 0.84 (1.5² + 0.5² ≤ (1.9·0.84)²), the big disc stays in
   σ ≥ 0.195 and at distance ≥ 1 from the pole for |t| ≥ 4;
 * ζ-growth ‖ζ(s)‖ ≤ C(|Im s|+3)^A on σ ≥ 0.15, ‖s−1‖ ≥ 1 and ‖ζ(2+it)‖ ≥ 1/3
   (Zeta23.RvM.zeta_growth_right / zeta_lower_bound_two, Zeta23/RvM/ZetaGrowth.lean);
 * |t| < 4 by the finite constant N(−4, 5].
-/


open Complex Set Filter Topology Metric

noncomputable section

namespace Zeta23.RvM













/-- The same, in H-RvM's vocabulary (Z.N at Z := zetaZeroConfig). -/
theorem zetaZeroConfig_local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  simpa only [zetaZeroConfig_N] using zeta_local_zero_count

end Zeta23.RvM
end
end

-- from Zeta23.RvM.Statement
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Statement.lean — Riemann–von Mangoldt assembly:
  Zeta23.RvM.riemannVonMangoldt (hΓ : GammaFacts) : RiemannVonMangoldt zetaZeroConfig
from Zeta23.RvM.rvM_main (MainTerm.lean) and Zeta23.RvM.zetaZeroConfig_local_count
(LocalCount.lean). Conditional on the Γ-facts by design (Stirling enters only through
`GammaFacts`).
-/

noncomputable section

namespace Zeta23.RvM

/-- **H-RvM for Mathlib's ζ**, given the Γ-facts. -/
theorem riemannVonMangoldt (hΓ : GammaFacts) : RiemannVonMangoldt zetaZeroConfig :=
  ⟨rvM_main hΓ, zetaZeroConfig_local_count⟩

end Zeta23.RvM
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

/-- **Theorem A**, two hypotheses (EF_lit, RvM): (2/3 − ε)·N(T,2T) ≤ N₀*(T,2T). -/
theorem thmA₂ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA3 hEF hRvM gammaFacts






end TwoHyp

/-! ## One-hypothesis forms: H-RvM is a theorem given the proved Γ-facts
(local count + folded argument principle + Backlund; Zeta23/RvM/*). -/

section OneHyp

/-- **H-RvM for ζ, unconditionally** (from the RvM development and the proved Γ-facts). -/
theorem riemannVonMangoldt_zeta : RiemannVonMangoldt zetaZeroConfig :=
  RvM.riemannVonMangoldt gammaFacts


variable (hEF : EF.EF_lit zetaZeroConfig)
include hEF







end OneHyp

/-! ## Unconditional forms: the explicit formula is a theorem
(Zeta23.WeilEF.EF_lit_zetaZeroConfig — Weil/Riemann–von Mangoldt explicit formula for ζ,
literature form [eq:EFstd], proved from Mathlib's functional equation by contour integration).
These are the headline statements of the formalization: no hypotheses at all. -/

section Unconditional









end Unconditional

section AFortiori



end AFortiori

section UnconditionalAFortiori



end UnconditionalAFortiori


end Zeta23
end
open Filter
open Zeta23
variable (hEF : EF.EF_lit zetaZeroConfig)
include hEF

theorem solution :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA₂ hEF riemannVonMangoldt_zeta
