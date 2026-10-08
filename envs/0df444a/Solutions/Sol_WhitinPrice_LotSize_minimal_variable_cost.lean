-- Prove2me | solution 1 for WhitinPrice.LotSize.minimal_variable_cost
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:30:10.062333+00:00
-- url     : https://prove2.me/submissions/7e52e54d-b063-48ea-a137-77e06e4d292f

import Definitions.Def_WhitinPrice_LotSize_Model

set_option autoImplicit false
open WhitinPrice.LotSize

theorem solution (S I C k D : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C) (hD : 0 < D) :
    tvc S I C k D (Real.sqrt (2 * D * S / (I * C))) =
      Real.sqrt (2 * D * S * I * C) + k * D := by
  let q := Real.sqrt (2 * D * S / (I * C))
  have hIC : 0 < I * C := mul_pos hI hC
  have hrad : 0 < 2 * D * S / (I * C) := by positivity
  have hq : 0 < q := Real.sqrt_pos.2 hrad
  have hsq : q ^ 2 * (I * C) = 2 * D * S := by
    dsimp [q]
    rw [Real.sq_sqrt (le_of_lt hrad)]
    exact div_mul_cancel₀ _ (ne_of_gt hIC)
  have hopt : tvc S I C k D q = q * (I * C) + k * D := by
    unfold tvc InventoryControl.eoqCost
    field_simp [ne_of_gt hq]
    nlinarith [hsq]
  have hroot : q * (I * C) = Real.sqrt (2 * D * S * I * C) := by
    have hp : 0 ≤ 2 * D * S * I * C := by positivity
    have hs := Real.sq_sqrt hp
    have hsnonneg := Real.sqrt_nonneg (2 * D * S * I * C)
    have hprod := congrArg (fun z : ℝ => z * (I * C)) hsq
    have hprodpos : 0 < q * (I * C) := mul_pos hq hIC
    nlinarith only [hs, hprod, hsnonneg, hprodpos]
  change tvc S I C k D q = _
  rw [hopt, hroot]

