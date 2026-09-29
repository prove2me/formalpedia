-- Prove2me | solution 1 for Zeta23.PrimeSide.evBound_of_eventuallyAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:07:57.348284+00:00
-- url     : https://prove2.me/submissions/34840f89-083d-4dbf-babb-eb26b20848e4

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideTemp

-- from Zeta23.PrimeSideB.Concrete
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
# The concrete prime-side data as an instance of the abstract layer
Small, dependency-light file (imports only `PrimeSideA.Basic` and `PrimeSideTemp`):

* `Params.toSetting P T = ⟨T, λ, w⟩`, `Params.localFun P T = ⟨φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b⟩(T)` and the
  `rfl` bridges (`trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T`, …);
* `PrimeSide.LocalHypsEventually cϱ P` — "the taper facts `LocalHyps` hold for the concrete data for
  all large `T`" (proved in `Zeta23/PrimeSideA/Bridge.lean`);
* `PrimeSide.evBound_of_eventuallyAt` — an `EventuallyAt`-form result specialised to the concrete
  data is an `EvBound` in `T`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace Params
variable (P : Params) (T : ℝ)



@[simp] lemma toSetting_T : (P.toSetting T).T = T := rfl
@[simp] lemma toSetting_lam : (P.toSetting T).lam = P.lam := rfl
@[simp] lemma toSetting_w : (P.toSetting T).w = P.w := rfl
@[simp] lemma toSetting_L : (P.toSetting T).L = P.L T := rfl
@[simp] lemma toSetting_X : (P.toSetting T).X = P.X T := rfl
@[simp] lemma toSetting_l : (P.toSetting T).l = l T := rfl
@[simp] lemma toSetting_ell1 : (P.toSetting T).ell1 = ell1 T := rfl
@[simp] lemma toSetting_d : (P.toSetting T).d = P.d T := rfl
@[simp] lemma toSetting_tau (k : ℤ) : (P.toSetting T).tau k = P.tau T k := rfl
@[simp] lemma localFun_a : (P.localFun T).a = P.a T := rfl
@[simp] lemma localFun_b : (P.localFun T).b = P.b T := rfl
@[simp] lemma localFun_Phi : (P.localFun T).Phi = P.PhiR T := rfl
@[simp] lemma localFun_g : (P.localFun T).g = P.g T := rfl
@[simp] lemma localFun_phiHat : (P.localFun T).phiHat = P.phiHatR T := rfl

end Params

namespace PrimeSide

variable (P : Params) (T : ℝ)





variable {P}




end PrimeSide

end Zeta23

end
open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (P : Params) (T : ℝ)
variable {P}

theorem solution {cϱ : ℝ} (hLoc : LocalHypsEventually cϱ P)
    {f g : Setting → LocalFun → ℝ}
    (h : ∃ C : ℝ, EventuallyAt cϱ P.lam (fun p F => |f p F| ≤ C * g p F))
    (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (P.localFun T)) :
    EvBound (fun T => f (P.toSetting T) (P.localFun T))
      (fun T => g (P.toSetting T) (P.localFun T)) := by
  obtain ⟨T₀, hT₀⟩ := hLoc
  obtain ⟨C, T₁, hT₁⟩ := h
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hg
  refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
  have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
  have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  calc |f (P.toSetting T) (P.localFun T)| ≤ C * g (P.toSetting T) (P.localFun T) :=
        hT₁ _ _ rfl h1 (hT₀ T h0)
    _ ≤ max C 1 * g (P.toSetting T) (P.localFun T) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hT₂ T h2)
