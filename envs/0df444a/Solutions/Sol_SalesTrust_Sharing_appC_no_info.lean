-- Prove2me | solution 1 for SalesTrust.Sharing.appC_no_info
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:53:36.77555+00:00
-- url     : https://prove2.me/submissions/5bad0abf-d1dd-4fd2-b447-42a44703c3c1

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

open SalesTrust.Sharing in
theorem solution (P : Params) (hS : P.Standing) (qH qL : ℝ) (hqL : 0 < qL) (hlt : qL < qH) :
    punish P < piR P.VH qH - TneH P qH qL + cont P ⟨qH, TneH P qH qL, qL, TneL P qL⟩ ∧
      piR P.VL qH - TneH P qH qL < piR P.VL qL - TneL P qL := by
  obtain ⟨hp0, hp1, hV, _, hd0, hd1⟩ := hS
  have hg : ∀ q, gap P q = (P.VH - P.VL) * q := fun q => by unfold gap piR; ring
  have hD : 0 < P.VH - P.VL := by linarith
  unfold punish cont staticRent retailerProfit TneH TneL
  simp only [hg]
  have ht : P.δ / (1 - P.δ) * (1 - P.δ) = P.δ := div_mul_cancel₀ _ (by linarith)
  set t := P.δ / (1 - P.δ) with htdef
  constructor
  · have hprod : t * (1 - P.δ) * (P.p * (P.VH - P.VL) * (qL - qSL P)) =
        P.δ * (P.p * (P.VH - P.VL) * (qL - qSL P)) := by rw [ht]
    have hpos : 0 < (P.VH - P.VL) * qL := mul_pos hD hqL
    nlinarith [hprod, hpos]
  · unfold piR
    nlinarith [mul_pos hD (sub_pos.mpr hlt)]
