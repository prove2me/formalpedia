-- Prove2me | solution 1 for Zeta23.GzGp.phiHat_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:46:34.755869+00:00
-- url     : https://prove2.me/submissions/c190e526-6756-475f-b230-d8200d8a671f

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses

-- from Zeta23.Hypotheses.GzGp
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses/GzGp.lean — the H-EF bridge between the two expressions of [eq:Gdef]:  Z.Gz P T (zero side, Σ_ρ m_ρ φ̂(γ_ρ−τ_k)φ̂(γ_ρ−τ_l))
                  = P.Gp T  (prime side, ∫ φ̂(τ−τ_k)φ̂(τ−τ_l)ν_X(τ)dτ),
"the two expressions agreeing by Proposition [prop:EF]" — here: by hypothesis H-EF applied to
f = f_k, g = f_l, using h_{f_k}(z) = φ̂(z − τ_k) and "since φ̂ is real on ℝ we have
conj φ̂(conj z) = φ̂(z)" ([subsec:family] after [eq:fk]).
What this does and does not test: it checks the paper's internal consistency between [eq:Wdef],
[eq:fk], [eq:Gdef] and the form of [eq:EF] (conjugations, shifts, realness, support, X = e^L);
it does not test the 2π/sign normalisation inside ν_X, because [eq:EF] enters as the hypothesis
H-EF in the paper's own form — that normalisation is tested in Zeta23/ExplicitFormula.lean
(literature form ⇒ ExplicitFormulaPaper).
Taper regularity (φ ∈ C², supp φ ⊆ [−L/2, L/2]; Zeta23/Taper.lean) enters as
hypotheses. Helper lemmas are namespaced Zeta23.GzGp to avoid clashing with Zeta23/Taper.lean's
Params.phiHat_conj / Params.phiHat_ofReal (same statements; proved here independently so
this file depends only on Zeta23.Hypotheses).
-/

open scoped ComplexConjugate
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

namespace GzGp

variable (P : Params) (T : ℝ)

lemma integral_comp_neg_real (g : ℝ → ℂ) : (∫ x : ℝ, g (-x)) = ∫ x : ℝ, g x := by
  have h := Measure.integral_comp_mul_left g (-1)
  simp only [neg_mul, one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  exact h

/-- φ is even: φ(−u) = φ(u)  ([subsec:family]: "φ ∈ C_c³(ℝ) is even"). -/
lemma phi_neg (u : ℝ) : P.phi T (-u) = P.phi T u := by simp [Params.phi, abs_neg]








end GzGp



end Zeta23
end
open scoped ComplexConjugate
open Complex MeasureTheory Set
open Zeta23
open GzGp
variable (P : Params) (T : ℝ)

theorem solution (z : ℂ) : P.phiHat T (conj z) = conj (P.phiHat T z) := by
  show (∫ u : ℝ, (P.phi T u : ℂ) * cexp (I * conj z * (u : ℂ)))
      = conj (∫ u : ℝ, (P.phi T u : ℂ) * cexp (I * z * (u : ℂ)))
  calc (∫ u : ℝ, (P.phi T u : ℂ) * cexp (I * conj z * (u : ℂ)))
      = ∫ u : ℝ, (fun v : ℝ => conj ((P.phi T v : ℂ) * cexp (I * z * (v : ℂ)))) (-u) := by
        congr 1
        ext u
        simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
          phi_neg, Complex.ofReal_neg, map_neg]
        congr 2
        ring
    _ = ∫ v : ℝ, conj ((P.phi T v : ℂ) * cexp (I * z * (v : ℂ))) :=
        integral_comp_neg_real (fun v : ℝ => conj ((P.phi T v : ℂ) * cexp (I * z * (v : ℂ))))
    _ = conj (∫ v : ℝ, (P.phi T v : ℂ) * cexp (I * z * (v : ℂ))) := integral_conj
