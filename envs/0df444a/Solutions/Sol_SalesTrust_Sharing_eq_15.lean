-- Prove2me | solution 1 for SalesTrust.Sharing.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:47:55.351264+00:00
-- url     : https://prove2.me/submissions/6d340349-017e-42e8-8041-64eac3516c83

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model
set_option autoImplicit false

open SalesTrust.Sharing

theorem solution (P : Params) (hS : P.Standing) :
    retailerProfit P (menuNE P) =
        P.p * (P.VH - P.VL) * (P.VL - P.p * P.VH) / (2 * (1 - P.p)) +
          P.δ * (1 - P.δ) * (P.p ^ 2 * (P.VH - P.VL) ^ 2 / (2 * (1 - P.p))) ∧
      staticRent P = P.p * (P.VH - P.VL) * (P.VL - P.p * P.VH) / (2 * (1 - P.p)) := by
  obtain ⟨h0, h1, -, -, -, -⟩ := hS
  have hp : (1 - P.p) ≠ 0 := by linarith
  constructor
  · simp only [retailerProfit, menuNE, TSH, TSL, qSL, piR]
    field_simp
    ring
  · simp only [staticRent, gap, qSL, piR]
    field_simp
    ring
