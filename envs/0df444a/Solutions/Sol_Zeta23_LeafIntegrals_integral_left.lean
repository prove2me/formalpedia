-- Prove2me | solution 1 for Zeta23.LeafIntegrals.integral_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:45:07.104399+00:00
-- url     : https://prove2.me/submissions/fcf1a532-cf35-4ec6-9fec-0a42c140a051

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

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

theorem solution (T : ℝ) (hT : 0 < T) :
    ∫ τ in T..(2 * T), ((1 + (τ - T)) ^ 2)⁻¹ ≤ 1 := by
  have hderiv : ∀ x ∈ uIcc T (2 * T),
      HasDerivAt (fun τ : ℝ => -(1 + (τ - T))⁻¹) (((1 + (x - T)) ^ 2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hpos : (1 + (x - T)) ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun τ : ℝ => 1 + (τ - T)) 1 x := by
      simpa using ((hasDerivAt_id x).sub_const T).const_add 1
    have h2 := (h1.inv hpos).neg
    have heq : -(-1 / (1 + (x - T)) ^ 2) = ((1 + (x - T)) ^ 2)⁻¹ := by
      rw [neg_div, neg_neg, one_div]
    exact heq ▸ h2
  have hcont : ContinuousOn (fun x : ℝ => ((1 + (x - T)) ^ 2)⁻¹) (uIcc T (2 * T)) := by
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; have : 0 < 1 + (x - T) := by linarith [hx.1]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have h1T : 0 < 1 + T := by linarith
  simp only [sub_self, add_zero, inv_one]
  rw [show 2 * T - T = T by ring]
  have : 0 < (1 + T)⁻¹ := by positivity
  linarith
