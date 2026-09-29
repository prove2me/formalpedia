-- Prove2me | solution 1 for Zeta23.PrimeSide.integral_Mfar_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:06:15.927745+00:00
-- url     : https://prove2.me/submissions/9153703b-89a9-4157-a92d-fc02cb94e3ce

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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Definitions.Def_Zeta23_PrimeSideA_EndsNu

-- from Zeta23.PrimeSideA.EndsNu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], the two one-dimensional ν-weighted ψ estimates feeding the 𝓔₂ bound
(§5.3 of the paper).  Consumed by Zeta23/PrimeSideA/EndsE2.lean.

* N1 `nu_weight_bound` (§5.3: "In the second factor, the range |τ'−τ_k| ≤ 2T has |τ'| ≤ 4T and
  contributes at most 2Ψ₀B; on |τ'−τ_k| =: r > 2T we have |τ'| ≤ 2r, |ν_X(τ')| ≤ B + log(r/T) and
  ψ(r) ≤ c_ϱ r⁻², contributing ≪ B/T. So the second factor is ≤ 3Ψ₀B uniformly in k."):
      ∫_ℝ ψ(τ−a) |ν_X(τ)| dτ ≤ (2Ψ + 5c_ϱ)·B   for a ∈ I = [T,2T],  Ψ := 4 + 2 log(c_ϱL/4w) ≥ Ψ₀.
  Route (constants only differ): |ν_X(τ)| ≤ B + log⁺(|τ|/4T) ≤ B + 2√(|τ|/4T) ≤ B + 2 + 2√(|τ−a|/4T)
  for |a| ≤ 2T, so the integral is ≤ (B+2)∫ψ + T^{-1/2}∫ψ(r)√|r| dr ≤ (B+2)·2Ψ + 2L + 4c_ϱ/w.
* N2 `nu_grid_bound` (§5.3: "The sum over k of the first factor equals ∫_{τ∉I}|ν_X(τ)|σ(τ)dτ with
  σ(τ) := Σ_{k<d} ψ(τ−τ_k) … Hence ∫_{τ∉I}|ν_X|σ ≪ BLl"):
      ∫_{ℝ∖I} |ν_X(τ)| σ(τ) dτ ≤ CN2(c_ϱ)·B·L·l.
Here ψ = `psiA cϱ p` [eq:psidef], B = `B` = l + 4√X and `NuBound p` = [eq:Bdef]
(discharged by nuX_abs_le), all from Zeta23/PrimeSideA/EndsCore.lean.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}









/-! ### N2: reduction to the half-line and the majorant -/





















/-! ### N2: integrating the majorant -/


/-- rpow form of the far majorant on Δ > 0. -/
lemma Mfar_eq_rpow (hT : 0 < p.T) {Δ : ℝ} (hΔ : 0 < Δ) :
    Mfar cϱ p B Δ = p.d * (cϱ / p.w) *
      (B * Δ ^ (-2:ℝ) + (2 / Real.sqrt p.T) * Δ ^ (-(3/2):ℝ)) := by
  unfold Mfar
  have hw : Δ ^ (-2:ℝ) = (Δ ^ 2)⁻¹ := by rw [Real.rpow_neg hΔ.le, Real.rpow_two]
  have h32 : Δ ^ (-(3/2):ℝ) = Δ ^ (1/2:ℝ) / Δ ^ 2 := by
    rw [show (-(3 / 2) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hΔ, Real.rpow_two]
  rw [hw, h32, Real.sqrt_div hΔ.le, Real.sqrt_eq_rpow]
  have : Δ ^ 2 ≠ 0 := by positivity
  have : Real.sqrt p.T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  field_simp











end PrimeSide
end Zeta23
end
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem solution (hF : LocalHypsCoreW cϱ p F) (hB : 0 ≤ B) (hT : 1 ≤ p.T) :
    ∫ Δ in Ioi (2 * p.T), Mfar cϱ p B Δ ≤ p.d / p.T * (cϱ / p.w) * (B / 2 + 4) := by
  have hT0 : 0 < p.T := by linarith
  have h2T : 0 < 2 * p.T := by linarith
  have hc : (0:ℝ) ≤ cϱ := by linarith [hF.four_le_cϱ]
  have hw : 0 < p.w := by linarith [hF.one_le_w]

  have hI2 := integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) h2T
  have hI32 := integral_Ioi_rpow_of_lt (by norm_num : (-(3/2):ℝ) < -1) h2T
  have hint2 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) h2T
  have hint32 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2):ℝ) < -1) h2T
  have e : ∫ Δ in Ioi (2 * p.T), Mfar cϱ p B Δ = p.d * (cϱ / p.w) *
      (B * (∫ Δ in Ioi (2 * p.T), Δ ^ (-2:ℝ))
        + (2 / Real.sqrt p.T) * ∫ Δ in Ioi (2 * p.T), Δ ^ (-(3/2):ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun Δ hΔ => Mfar_eq_rpow (cϱ := cϱ) hT0 (lt_trans h2T hΔ)),
      integral_const_mul, integral_add (hint2.const_mul _) (hint32.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [e, hI2, hI32]
  -- evaluate: (2T)^{-1} and 2(2T)^{-1/2}; bound (2T)^{-1/2} ≤ 1/√T
  have ev1 : -(2 * p.T) ^ ((-2:ℝ) + 1) / ((-2:ℝ) + 1) = 1 / (2 * p.T) := by
    rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]; field_simp
  have ev2 : -(2 * p.T) ^ (-(3/2:ℝ) + 1) / (-(3/2:ℝ) + 1) = 2 * (2 * p.T) ^ (-(1/2):ℝ) := by
    rw [show (-(3/2:ℝ)) + 1 = -(1/2) by norm_num]; field_simp
  rw [ev1, ev2]
  have hsq : (2 * p.T) ^ (-(1/2):ℝ) ≤ 1 / Real.sqrt p.T := by
    rw [Real.rpow_neg h2T.le, ← Real.sqrt_eq_rpow, one_div]
    exact inv_anti₀ (Real.sqrt_pos.mpr hT0) (Real.sqrt_le_sqrt (by linarith))
  have hsT : 0 < Real.sqrt p.T := Real.sqrt_pos.mpr hT0
  have key : B * (1 / (2 * p.T)) + 2 / Real.sqrt p.T * (2 * (2 * p.T) ^ (-(1/2):ℝ))
      ≤ 1 / p.T * (B / 2 + 4) := by
    have h1 : 2 / Real.sqrt p.T * (2 * (2 * p.T) ^ (-(1/2):ℝ)) ≤ 2 / Real.sqrt p.T * (2 * (1 / Real.sqrt p.T)) := by
      gcongr
    have h2 : 2 / Real.sqrt p.T * (2 * (1 / Real.sqrt p.T)) = 4 / p.T := by
      rw [show (4:ℝ) / p.T = 4 / (Real.sqrt p.T * Real.sqrt p.T) by rw [Real.mul_self_sqrt hT0.le]]
      field_simp; ring
    have h3 : B * (1 / (2 * p.T)) = 1 / p.T * (B / 2) := by field_simp
    rw [h3]
    have : 1 / p.T * (B / 2 + 4) = 1 / p.T * (B / 2) + 4 / p.T := by field_simp
    rw [this]
    linarith
  calc p.d * (cϱ / p.w) * (B * (1 / (2 * p.T)) + 2 / Real.sqrt p.T * (2 * (2 * p.T) ^ (-(1/2):ℝ)))
      ≤ p.d * (cϱ / p.w) * (1 / p.T * (B / 2 + 4)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = p.d / p.T * (cϱ / p.w) * (B / 2 + 4) := by field_simp
