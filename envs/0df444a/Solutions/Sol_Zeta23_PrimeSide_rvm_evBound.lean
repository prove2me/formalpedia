-- Prove2me | solution 1 for Zeta23.PrimeSide.rvm_evBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:38:03.72143+00:00
-- url     : https://prove2.me/submissions/736e465e-82ce-4967-81fb-a227a1f0cb78

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
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

-- from Zeta23.PrimeSideB.Traces
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




end PrimeSide

end Zeta23

end
open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
open PaperParams
variable (P : Params)
variable {P}

theorem solution {Z : ZeroConfig} (hR : RiemannVonMangoldt Z) :
    EvBound (fun T => (Z.N T (2 * T) : ℝ) - T * ell1 T / (2 * π)) l := by
  obtain ⟨C, T₀, hC⟩ := hR.main
  refine ⟨2 * max C 1, by positivity, max T₀ (4 * π ^ 2), fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hT4 : 4 * π ^ 2 ≤ T := (le_max_right _ _).trans hT
  have hπ := Real.pi_pos
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT4
  have h1 := hC T hT₀
  have h2 : T / (2 * π) * ell1 T = T * ell1 T / (2 * π) := by ring
  rw [h2] at h1
  -- log T ≤ 2 l T  ⟺  log T ≤ 2 log T − 2 log(2π)  ⟺  2 log (2π) ≤ log T ⟺ (2π)² ≤ T
  have hl : Real.log T ≤ 2 * l T := by
    unfold l
    rw [Real.log_div hT0.ne' (by positivity)]
    have : Real.log ((2 * π) ^ 2) ≤ Real.log T :=
      Real.log_le_log (by positivity) (by nlinarith only [hT4])
    rw [Real.log_pow] at this
    push_cast at this
    linarith only [this]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by nlinarith only [hT4, hπ, Real.pi_gt_three])
  calc |(Z.N T (2 * T) : ℝ) - T * ell1 T / (2 * π)| ≤ C * Real.log T := h1
    _ ≤ max C 1 * Real.log T := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
    _ ≤ max C 1 * (2 * l T) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = 2 * max C 1 * l T := by ring
