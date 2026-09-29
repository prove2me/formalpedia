-- Prove2me | solution 1 for Zeta23.PrimeSide.inner_ibp_phase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:38:18.392943+00:00
-- url     : https://prove2.me/submissions/b964bbce-9459-4b1f-8007-4e93959c6b8c

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
import Definitions.Def_Zeta23_PrimeSideA_Defs

-- from Zeta23.PrimeSideA.CrossMuPCore
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Analytic core of [prop:cross] (i): the double integration by parts for `𝓜[u, cos(·y)]`

See `Zeta23/PrimeSideA/CrossMuP.lean` for the statement of [prop:cross](i) and the paper text.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

section CrossMuPCore
variable {Φ : ℝ → ℝ} {T : ℝ}










end CrossMuPCore

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem solution (hΦ : ContDiff ℝ 1 Φ) {y : ℝ} (hy : y ≠ 0) (θ τ : ℝ) :
    ∫ τ' in T..(2 * T), Φ (τ - τ') ^ 2 * Real.cos (τ' * y + θ)
      = (Φ (τ - 2 * T) ^ 2 * Real.sin (2 * T * y + θ) - Φ (τ - T) ^ 2 * Real.sin (T * y + θ)) / y
        + y⁻¹ * ∫ τ' in T..(2 * T), deriv (fun x => Φ x ^ 2) (τ - τ') * Real.sin (τ' * y + θ) := by
  set Ψ : ℝ → ℝ := fun x => Φ x ^ 2 with hΨdef
  have hΨ : ContDiff ℝ 1 Ψ := hΦ.pow 2
  have hΨd : ∀ x, HasDerivAt Ψ (deriv Ψ x) x := fun x =>
    (hΨ.differentiable one_ne_zero x).hasDerivAt
  have hΨ'c : Continuous (deriv Ψ) := hΨ.continuous_deriv le_rfl
  have hu : ∀ x ∈ Set.uIcc T (2 * T), HasDerivAt (fun τ' => Ψ (τ - τ')) (-deriv Ψ (τ - x)) x := by
    intro x _
    have h := (hΨd (τ - x)).comp x ((hasDerivAt_id x).const_sub τ)
    simpa [Function.comp_def] using h
  have hv : ∀ x ∈ Set.uIcc T (2 * T),
      HasDerivAt (fun τ' => Real.sin (τ' * y + θ) / y) (Real.cos (x * y + θ)) x := by
    intro x _
    have h := ((((hasDerivAt_id x).mul_const y).add_const θ).sin).div_const y
    simpa [mul_div_assoc, div_self hy] using h
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    ((hΨ'c.comp (continuous_const.sub continuous_id)).neg.intervalIntegrable _ _)
    ((Real.continuous_cos.comp ((continuous_id.mul continuous_const).add
      continuous_const)).intervalIntegrable _ _)
  simp only [hΨdef] at hibp ⊢
  rw [hibp]
  have e : ∫ x in T..(2 * T), -deriv (fun x => Φ x ^ 2) (τ - x) * (Real.sin (x * y + θ) / y)
      = -(y⁻¹ * ∫ x in T..(2 * T), deriv (fun x => Φ x ^ 2) (τ - x) * Real.sin (x * y + θ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; ext x; field_simp
  rw [e]
  field_simp
  ring
