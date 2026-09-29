-- Prove2me | solution 1 for Zeta23.thmA3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:51:52.543487+00:00
-- url     : https://prove2.me/submissions/afece794-d4f6-4569-87b6-4d10e216aa67

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
import Theorems.Thm_Zeta23_Cheb_chebyshevMertens
import Theorems.Thm_Zeta23_EF_explicitFormulaPaper_of_lit
import Theorems.Thm_Zeta23_MV_eigen_bound
import Theorems.Thm_Zeta23_MV_mvDiag_of_eigenBound
import Theorems.Thm_Zeta23_MVHilbert_of_diag
import Theorems.Thm_Zeta23_PrimeSide_concreteFacts
import Theorems.Thm_Zeta23_PrimeSide_localHypsEventually
import Theorems.Thm_Zeta23_PrimeSide_tracesBounds_of_facts
import Theorems.Thm_Zeta23_thmA_of_traces

-- from Zeta23.Defs.Profile
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs/Profile.lean — a concrete taper profile.
The paper: "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)" [subsec:family]. Mathlib's Real.smoothTransition is such a function (even C^∞), so the
headline theorems need not quantify over ϱ.
-/

noncomputable section

namespace Zeta23

/-- Real.smoothTransition is a taper profile in the paper's sense. -/
theorem taperProfile_smoothTransition : TaperProfile Real.smoothTransition where
  contDiff := Real.smoothTransition.contDiff
  monotone := Real.smoothTransition.monotone
  eq_zero := fun _ hx => Real.smoothTransition.zero_of_nonpos hx
  eq_one := fun _ hx => Real.smoothTransition.one_of_one_le hx


theorem taperProfile_stdProfile : TaperProfile stdProfile := taperProfile_smoothTransition


end Zeta23
end
end

-- from Zeta23.MV
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/MV.lean — the Montgomery–Vaughan weighted Hilbert inequality: literature (diagonal, y = x)
form ⇒ the bilinear (x, z) form H-MV of Zeta23/Hypotheses.lean.

Purpose (trust reduction): Zeta23.MVHilbert C — what [prop:PP]/[prop:cross] consume —
is the BILINEAR inequality |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ C (Σ|x_r|²/δ_r)^{1/2} (Σ|z_r|²/δ_r)^{1/2}.
The published theorem is the case z = x.  The paper, [lem:MV] and its proof,
verbatim: "Lemma (Montgomery–Vaughan). Let λ_1,…,λ_R be distinct real numbers and
δ_r := min_{s≠r}|λ_r−λ_s|. Then for all complex x_r, z_r,
  |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ (3π/2)(Σ_r |x_r|²/δ_r)^{1/2}(Σ_r |z_r|²/δ_r)^{1/2}.
Proof. For z = x this is the weighted ("generalised") Hilbert inequality of Montgomery and Vaughan
[MV74, Theorem 2]; see also [Mon94, Chapter 7]. Any absolute constant in place of 3π/2 would
suffice below. In general, let H be the Hermitian matrix with entries i/(λ_r−λ_s) off the
diagonal and 0 on it, and Δ := diag(δ_r^{1/2}). The case z = x says |y*(ΔHΔ)y| ≤ (3π/2)‖y‖₂² for
all y, i.e. ‖ΔHΔ‖ ≤ 3π/2 since ΔHΔ is Hermitian; hence
|x*Hz| = |(Δ⁻¹x)*(ΔHΔ)(Δ⁻¹z)| ≤ (3π/2)‖Δ⁻¹x‖₂‖Δ⁻¹z‖₂."

Literature statement transcribed (H. L. Montgomery and R. C. Vaughan, "Hilbert's inequality",
J. London Math. Soc. (2) 8 (1974), 73–82, Theorem 2 = the "generalised" weighted form, their
(1.8)): if λ_1,…,λ_R are distinct reals, δ_r := min_{s≠r}|λ_r − λ_s|, then for all complex x_r,
  |Σ_{r≠s} x_r x̄_s / (λ_r − λ_s)| ≤ (3π/2) Σ_r |x_r|²/δ_r.
(The constant 3π/2 was later improved — Preissmann 1984 — but the paper says any absolute
constant suffices, and the headline result only needs ∃ C, so C is kept abstract: MVDiag C.)
As in Zeta23.MVHilbert we allow any admissible δ (δ_r > 0, δ_r ≤ |λ_r − λ_s| for s ≠ r); the right
side is antitone in δ, so this is equivalent to the min-gap δ of the literature.

We derive the bilinear form with constant 2C (not C) by POLARIZATION of the sesquilinear form plus
the scaling x ↦ t x, z ↦ z/t — an elementary route that avoids operator norms; the factor 2 is
immaterial (∃ C).  Result: Zeta23.MVHilbert_of_diag : 0 ≤ C → MVDiag C → MVHilbert (2 * C), and
Zeta23.exists_MVHilbert_of_diag for the ∃-forms used by PaperInputs.MV.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23


namespace MV

variable {ι : Type} [Fintype ι] [DecidableEq ι]
















end MV


/-- ∃-form, matching PaperInputs.MV's shape: (∃ C > 0, MVDiag C) → (∃ C > 0, MVHilbert C). -/
theorem exists_MVHilbert_of_diag (h : ∃ C : ℝ, 0 < C ∧ MVDiag C) :
    ∃ C : ℝ, 0 < C ∧ MVHilbert C := by
  obtain ⟨C, hC, hd⟩ := h
  exact ⟨2 * C, by positivity, MVHilbert_of_diag hC.le hd⟩

end Zeta23
end
end

-- from Zeta23.MV.Duality
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 4 — spectral reduction: `eigen_bound` ⇒ `MVDiag 13` ⇒ `∃ C, MVHilbert C`

With `k_{rs} := √δ_r √δ_s/(λ_r − λ_s)` (0 on the diagonal; real antisymmetric) the matrix
`M := i·K` is Hermitian.  Every eigen-pair `(ν, v)` of `M` (unit `v`, from Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`) satisfies the eigen-relation of `eigen_bound` with `μ := −ν`,
so `|ν| ≤ 13` for all eigenvalues (step 3).  Expanding in the eigenbasis
(`y* M y = Σ_i ν_i |(U*y)_i|²`, `Σ_i |(U*y)_i|² = Σ_i |y_i|²`) gives `|y* M y| ≤ 13 ‖y‖²`;
substituting `y_r := x_r/√δ_r` lands exactly on `MVDiag 13` (the literature / diagonal form of the
Montgomery–Vaughan weighted Hilbert inequality, Zeta23/MV.lean), and polarization
`exists_MVHilbert_of_diag` yields the bilinear H-MV of `Hypotheses.lean`.
-/

noncomputable section

open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV


variable {ι : Type} [Fintype ι] [DecidableEq ι]











/-- … hence the bilinear H-MV of `Hypotheses.lean` with constant `2C` (polarization). -/
theorem mvHilbert_of_eigenBound {C : ℝ} (hC : 0 < C) (hb : EigenBound C) :
    ∃ C' : ℝ, 0 < C' ∧ MVHilbert C' :=
  exists_MVHilbert_of_diag ⟨C, hC, mvDiag_of_eigenBound hb⟩

end MV
end Zeta23

end
end

-- from Zeta23.MV.Final
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The Montgomery–Vaughan weighted Hilbert inequality

`eigen_bound` (`Zeta23/MV/Eigen.lean`) is exactly `EigenBound 13`; the spectral reduction of
`Duality.lean` turns it into `MVDiag 13` and, via polarization (`Zeta23/MV.lean`), into the
bilinear `∃ C > 0, MVHilbert C` of `Hypotheses.lean` (C = 26) — discharging `PaperInputs.MV`.
-/

noncomputable section

namespace Zeta23
namespace MV

theorem eigenBound_thirteen : EigenBound 13 :=
  fun _ι _ _ _freq _δ h u hu μ heig => eigen_bound h u hu μ heig


/-- **H-MV:** `∃ C > 0, MVHilbert C` (the field `PaperInputs.MV`). -/
theorem mv_hilbert : ∃ C : ℝ, 0 < C ∧ MVHilbert C :=
  mvHilbert_of_eigenBound (by norm_num) eigenBound_thirteen

end MV
end Zeta23

end
end

-- from Zeta23.PrimeSideB.Traces
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# [thm:traces] for the concrete data — instantiating the abstract assembly
`Zeta23/PrimeSideB.lean` proves [thm:traces] for abstract real functions of `T`
(`PrimeSide.Facts D → TracesBounds …`).  This file plugs in the concrete objects:

* `Params.toSetting P T = ⟨T, λ, w⟩` and `Params.localFun P T = ⟨φ̂, Φ, A_φ, g, a, b⟩(T)` turn
  (`P : Params`, `T`) into the abstract prime-side layer (`Setting`, `LocalFun`), and
  `trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T` etc. hold by `rfl`;
* `PrimeSide.concreteData P Z` is the `Data P` record of the actual traces / 𝓜-terms / ∫μ² / Σa_n²g;
* `PrimeSide.concreteFacts` derives `Facts (concreteData P Z)` from `P.Valid`, `PaperInputs Z`
  (H-RvM, H-Γ, H-cheb, H-MV), [prop:trace]/[lem:ends]/[eq:Msplit]/[prop:mumu]/[prop:cross],
  [prop:PP] + sandwich, and `LocalHypsEventually cϱ P` (the taper facts [eq:psidef],
  [eq:abdef], [eq:gbounds], [eq:Phi2FT], [lem:poisson] … for the concrete φ — proved in
  `Zeta23/PrimeSideA/Bridge.lean` from Taper.lean / Poisson.lean);
* `thm_traces_of_localHyps : … → ThmTracesHyp P Z`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace PrimeSide

open PaperParams

variable (P : Params)


variable {P}



/-- **[thm:traces] for the concrete prime-side data**: the hypothesis `ThmTracesHyp P Z` of
`PrimeSideTemp.lean` follows from `P.Valid`, the published inputs `PaperInputs Z`, and the taper
facts for the concrete φ. -/
theorem thm_traces_of_localHyps {cϱ : ℝ} {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hLoc : LocalHypsEventually cϱ P) : ThmTracesHyp P Z :=
  tracesBounds_of_facts (concreteFacts hP inp hLoc)

end PrimeSide

end Zeta23

end
end

-- from Zeta23.PrimeSideB.Final
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# [thm:traces], final form: `P.Valid → PaperInputs Z → ThmTracesHyp P Z`
Three lines combining `Traces.lean` (the instantiated assembly, taking the
taper facts as `LocalHypsEventually`) with `Bridge.lean` (which proves them).  Kept in its own file
so that `Traces.lean` does not depend on the Taper/Poisson tree.
-/

noncomputable section

namespace Zeta23
namespace PrimeSide

/-- **Theorem [thm:traces]** (the paper §5 "Summary") for the concrete prime-side matrix
([eq:Gdef] 2nd expression) — i.e. the hypothesis `ThmTracesHyp P Z` derived from `P.Valid`
and the published inputs `PaperInputs Z` alone. -/
theorem thm_traces {P : Params} {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z) : ThmTracesHyp P Z :=
  thm_traces_of_localHyps hP inp (localHypsEventually hP)


end PrimeSide
end Zeta23

end
end

-- from Zeta23.Main
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Main.lean — ζ-level headline theorems: proofs.
Instantiates the abstract §6 assembly (Zeta23.Assembly, over an arbitrary ZeroConfig) at the
nontrivial zeros of Mathlib's riemannZeta (Zeta23.zetaZeros), and performs the λ → 1⁻ and
dyadic-summation wrappers. See Zeta23/Statement.lean for the definitions being talked about.
-/

open Filter Topology

noncomputable section

namespace Zeta23

section wrappers
variable (hs : ZetaSeam)












end wrappers

/-! ## Theorem A from PaperInputs + the thm:traces hypothesis

`thmA_of_traces` is a named declaration whose type shows exactly what is assumed: the
published inputs H : PaperInputs, a taper profile, and the thm:traces hypothesis
ThmTracesHyp (stated on the prime-side ν_X integrals). The zero-side block package and the
tail package are discharged from the sibling files. -/

section M1

open Assembly


lemma paramsOf_valid {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    (paramsOf ϱ lam).Valid := ⟨hϱ, h0, h1, le_rfl⟩






end M1

section M1BC

open Assembly



variable (H : PaperInputs zetaZeroConfig) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    (hTr : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 → ThmTracesHyp (paramsOf ϱ lam) zetaZeroConfig)
include H hϱ hTr





end M1BC

/-! ## Minimal trust base, displayed in the type

The literature-form explicit formula EF_lit ([eq:EFstd]) implies the paper form given
H-Γ (Zeta23.EF.explicitFormulaPaper_of_lit), and H-cheb is a theorem (Zeta23.Cheb.chebyshevMertens).
So the published inputs reduce to: EF_lit, Riemann–von Mangoldt (+ local count),
Montgomery–Vaughan, and the Γ-facts. -/

section TrustBase

/-- PaperInputs from the minimal trust base. -/
theorem PaperInputs.of_lit {Z : ZeroConfig} (hEF : EF.EF_lit Z) (hRvM : RiemannVonMangoldt Z)
    (hMV : ∃ C : ℝ, 0 < C ∧ MVHilbert C) (hΓ : GammaFacts) : PaperInputs Z :=
  ⟨EF.explicitFormulaPaper_of_lit Z hEF hΓ, hRvM, Cheb.chebyshevMertens, hMV, hΓ⟩


end TrustBase

section M1Std




end M1Std

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

/-- PaperInputs from (literature EF, RvM, Γ-facts) only: cheb and MV are theorems. -/
theorem PaperInputs.of_three {Z : ZeroConfig} (hEF : EF.EF_lit Z) (hRvM : RiemannVonMangoldt Z)
    (hΓ : GammaFacts) : PaperInputs Z :=
  PaperInputs.of_lit hEF hRvM MV.mv_hilbert hΓ

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









end Unconditional

section AFortiori



end AFortiori

section UnconditionalAFortiori



end UnconditionalAFortiori


end Zeta23
end
open Filter
open Zeta23
variable (hEF : EF.EF_lit zetaZeroConfig) (hRvM : RiemannVonMangoldt zetaZeroConfig) (hΓ : GammaFacts)
include hEF hRvM hΓ

theorem solution :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  let H := PaperInputs.of_three hEF hRvM hΓ
  thmA_of_traces H taperProfile_stdProfile fun _ h1 h2 =>
    PrimeSide.thm_traces (paramsOf_valid taperProfile_stdProfile (by linarith) h2.le) H
