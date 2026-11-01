-- Prove2me | solution 1 for SalesTrust.Sharing.eq_30
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:17:27.57795+00:00
-- url     : https://prove2.me/submissions/500795b9-0628-47db-afce-55c0c1c3410c

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

open SalesTrust.Sharing

theorem solution (P : Params) (hS : P.Standing) :
    retailerProfit P (menuE P) =
      P.p * (P.VH - P.VL) * (P.VL - P.p * P.VH) / (2 * (1 - P.p) * (1 + P.δ * P.p) ^ 2) +
        P.δ * P.p ^ 2 * (P.VH - P.VL) / (2 * (1 - P.p) * (1 + P.δ * P.p) ^ 2) *
          ((1 - P.p - P.δ * (1 + P.p + P.p ^ 2)) * P.VH +
            (1 + P.δ - P.p + 2 * P.δ * P.p) * P.VL) := by
  obtain ⟨hp0, hp1, -, -, hd0, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  have h2 : (1 + P.δ * P.p) ≠ 0 := by nlinarith
  simp only [retailerProfit, menuE, piR, qSL, TSH, TSL]
  field_simp
  ring
