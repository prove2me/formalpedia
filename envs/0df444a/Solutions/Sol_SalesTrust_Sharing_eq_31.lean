-- Prove2me | solution 1 for SalesTrust.Sharing.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:17:26.95684+00:00
-- url     : https://prove2.me/submissions/94721f08-f55d-416b-912d-05aa8a42eb8a

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

open SalesTrust.Sharing

theorem solution (P : Params) (hS : P.Standing) :
    retailerProfit P (menuE P) - retailerProfit P (menuNE P) =
      P.δ * P.p ^ 3 * (1 - P.δ) * (P.VH - P.VL) ^ 2 / (2 * (1 - P.p) * (1 + P.δ * P.p) ^ 2) *
        (1 - P.δ * (2 + P.δ * P.p)) := by
  obtain ⟨hp0, hp1, -, -, hd0, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  have h2 : (1 + P.δ * P.p) ≠ 0 := by nlinarith
  simp only [retailerProfit, menuE, menuNE, piR, qSL, TSH, TSL]
  field_simp
  ring
