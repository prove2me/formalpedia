-- Prove2me | solution 1 for RevShareCoord.Effort.Linear.supplier_profit_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:56:05.003869+00:00
-- url     : https://prove2.me/submissions/9ebc4b65-ef32-4eb8-ad71-3fe61b6f5524

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

open RevShareCoord.Effort.Linear in
theorem solution (τ c φ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    supplierProfitAt τ c φ (wholesalePrice τ c φ) =
      (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have hD : 0 < 1 + φ * (1 - 2 * τ ^ 2) := by nlinarith
  have hA : 0 < 1 - φ * τ ^ 2 := by nlinarith
  have hDne := hD.ne'
  have hφw : φ - wholesalePrice τ c φ = φ * (1 - c) * (1 - φ * τ ^ 2) / (1 + φ * (1 - 2 * τ ^ 2)) := by
    unfold wholesalePrice; rw [eq_div_iff hDne, sub_mul, div_mul_cancel₀ _ hDne]; ring
  have hlt : wholesalePrice τ c φ < φ := by
    have : 0 < φ - wholesalePrice τ c φ := by
      rw [hφw]; apply div_pos _ hD; apply mul_pos (mul_pos hφ0 (by linarith)) hA
    linarith
  have hq : orderQty τ φ (wholesalePrice τ c φ) = (1 - c) / (2 * (1 + φ * (1 - 2 * τ ^ 2))) := by
    unfold orderQty; rw [if_pos hlt, hφw]
    have : φ - φ ^ 2 * τ ^ 2 = φ * (1 - φ * τ ^ 2) := by ring
    rw [this]; field_simp
  unfold supplierProfitAt supplierProfit revenue price effort
  rw [hq]; unfold wholesalePrice
  field_simp; ring
