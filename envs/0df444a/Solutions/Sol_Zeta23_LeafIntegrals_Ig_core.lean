-- Prove2me | solution 1 for Zeta23.LeafIntegrals.Ig_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:43:39.475039+00:00
-- url     : https://prove2.me/submissions/fc3964bf-0ddc-4294-ab0a-e3d2e642d2c7

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Theorems.Thm_Zeta23_LeafIntegrals_integral_left
import Theorems.Thm_Zeta23_LeafIntegrals_integral_right

-- from Zeta23.Defs.LeafIntegrals
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
Zeta23/Defs/LeafIntegrals.lean — self-contained elementary integral bounds used as drop-ins by
§5's lem:ends (Zeta23/PrimeSideA/EndsE1.lean). Imports only Mathlib.
-/

open MeasureTheory Real Set

noncomputable section

namespace Zeta23.LeafIntegrals




/-! ## (W3) core: ∫ ψ(r)² (2+|r|)² dr ≤ 18 L² + 18 (c/w)² for any even 0 ≤ ψ ≤ L with ψ(r) ≤ c/(w r²) -/


end Zeta23.LeafIntegrals
end
open MeasureTheory Real Set
open Zeta23
open Zeta23.LeafIntegrals

theorem solution (T : ℝ) (hT : 0 < T) :
    ∫ τ in Icc T (2 * T), ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹ ≤ 2 := by
  have hle : T ≤ 2 * T := by linarith
  -- pointwise bound on [T,2T]
  have hpt : ∀ τ ∈ Icc T (2 * T), ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹ ≤
      ((1 + (τ - T)) ^ 2)⁻¹ + ((1 + (2 * T - τ)) ^ 2)⁻¹ := by
    intro τ hτ
    have ha : 0 < 1 + (τ - T) := by linarith [hτ.1]
    have hb : 0 < 1 + (2 * T - τ) := by linarith [hτ.2]
    have hA : 0 ≤ ((1 + (τ - T)) ^ 2)⁻¹ := by positivity
    have hB : 0 ≤ ((1 + (2 * T - τ)) ^ 2)⁻¹ := by positivity
    rcases min_choice (τ - T) (2 * T - τ) with h | h <;> rw [h] <;> linarith
  have hcontL : ContinuousOn (fun τ : ℝ => ((1 + (τ - T)) ^ 2)⁻¹) (Icc T (2 * T)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; have : 0 < 1 + (x - T) := by linarith [hx.1]
    positivity
  have hcontR : ContinuousOn (fun τ : ℝ => ((1 + (2 * T - τ)) ^ 2)⁻¹) (Icc T (2 * T)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; have : 0 < 1 + (2 * T - x) := by linarith [hx.2]
    positivity
  have hcontM : ContinuousOn (fun τ : ℝ => ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹) (Icc T (2 * T)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    have : 0 < 1 + min (x - T) (2 * T - x) := by
      rcases min_choice (x - T) (2 * T - x) with h | h <;> rw [h] <;> linarith [hx.1, hx.2]
    positivity
  calc ∫ τ in Icc T (2 * T), ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹
      ≤ ∫ τ in Icc T (2 * T), (((1 + (τ - T)) ^ 2)⁻¹ + ((1 + (2 * T - τ)) ^ 2)⁻¹) := by
        apply setIntegral_mono_on (hcontM.integrableOn_Icc) ((hcontL.add hcontR).integrableOn_Icc)
          measurableSet_Icc hpt
    _ = (∫ τ in T..(2 * T), ((1 + (τ - T)) ^ 2)⁻¹) + ∫ τ in T..(2 * T), ((1 + (2 * T - τ)) ^ 2)⁻¹ := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
          intervalIntegral.integral_add (hcontL.intervalIntegrable_of_Icc hle)
            (hcontR.intervalIntegrable_of_Icc hle)]
    _ ≤ 1 + 1 := add_le_add (integral_left T hT) (integral_right T hT)
    _ = 2 := by norm_num
