-- Prove2me | solution 1 for SalesTrust.Sharing.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:56:15.554992+00:00
-- url     : https://prove2.me/submissions/dfbec16d-6371-4cae-84ba-a4b00858d4ca

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

open SalesTrust.Sharing in
theorem solution (P : Params) (hS : P.Standing) (qH qL : ℝ) :
    (∀ TH TL : ℝ,
      (piR P.VL qL - TL + cont P ⟨qH, TH, qL, TL⟩ = punish P ∧
        piR P.VH qH - TH = piR P.VH qL - TL) ↔
      (TL = TneL P qL ∧ TH = TneH P qH qL)) ∧
    mfrProfit P ⟨qH, TneH P qH qL, qL, TneL P qL⟩ =
      P.p * piR P.VH qH + (1 - P.p) * piR P.VL qL - P.p * gap P qL +
        P.δ * P.p * (gap P qL - gap P (qSL P)) := by
  obtain ⟨_, _, _, _, _, hd1⟩ := hS
  have hg : gap P qL = piR P.VH qL - piR P.VL qL := rfl
  have ht : P.δ / (1 - P.δ) * (1 - P.δ) = P.δ := div_mul_cancel₀ _ (by linarith)
  unfold cont punish staticRent retailerProfit TneL TneH mfrProfit
  simp only [hg]
  set t := P.δ / (1 - P.δ) with htdef
  set A := piR P.VL qL
  set B := piR P.VH qL
  set C := piR P.VH qH
  set D := piR P.VL qH
  set gS := gap P (qSL P)
  refine ⟨fun TH TL => ?_, by ring⟩
  constructor
  · rintro ⟨h1, h2⟩
    have hTL : TL = A + P.δ * P.p * (B - A - gS) := by
      linear_combination (-(1 - P.δ)) * h1 +
        (P.p * (C - TH) + (1 - P.p) * (A - TL) - P.p * gS) * ht + P.δ * P.p * h2
    refine ⟨hTL, ?_⟩
    linear_combination (-1) * h2 + hTL
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, by ring⟩
    linear_combination (P.p * (B - A - gS)) * ht
