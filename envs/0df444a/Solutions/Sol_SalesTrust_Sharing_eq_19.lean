-- Prove2me | solution 1 for SalesTrust.Sharing.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:28:22.17834+00:00
-- url     : https://prove2.me/submissions/f8a0ce0f-c627-4c7d-a5fe-e8894d4f7aee

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

open SalesTrust.Sharing

theorem solution (P : Params) (hS : P.Standing) (qH qL : ℝ) :
    (∀ TH TL : ℝ,
      (piR P.VL qL - TL + cont P ⟨qH, TH, qL, TL⟩ = punish P ∧
        piR P.VH qH - TH + cont P ⟨qH, TH, qL, TL⟩ = piR P.VH qL - TL + punish P) ↔
      (TL = TeL P qL ∧ TH = TeH P qH qL)) ∧
    mfrProfit P ⟨qH, TeH P qH qL, qL, TeL P qL⟩ =
      P.p * piR P.VH qH + (1 - P.p) * piR P.VL qL - P.p * gap P qL +
        (1 + P.p) / (1 + P.δ * P.p) * (P.δ * P.p * (gap P qL - gap P (qSL P))) := by
  obtain ⟨hp0, hp1, -, -, hd0, hd1⟩ := hS
  have hd : (1 - P.δ) ≠ 0 := by linarith
  have hk : (1 + P.δ * P.p) ≠ 0 := by nlinarith
  refine ⟨fun TH TL => ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩, ?_⟩
  · simp only [cont, punish, retailerProfit, staticRent] at h1 h2
    have e1 : (1 - P.δ) * (piR P.VL qL - TL) + P.δ * (P.p * (piR P.VH qH - TH)
        + (1 - P.p) * (piR P.VL qL - TL)) - P.δ * (P.p * gap P (qSL P)) = 0 := by
      have := congrArg (fun z => (1 - P.δ) * z) h1
      field_simp at this
      linear_combination this
    have e2 : (1 - P.δ) * ((piR P.VH qH - TH) - (piR P.VL qL - TL) - (piR P.VH qL - piR P.VL qL))
        + P.δ * (P.p * (piR P.VH qH - TH)
        + (1 - P.p) * (piR P.VL qL - TL)) - P.δ * (P.p * gap P (qSL P)) = 0 := by
      have := congrArg (fun z => (1 - P.δ) * z) h2
      field_simp at this
      linear_combination this
    have e3 : (piR P.VH qH - TH) - 2 * (piR P.VL qL - TL) - gap P qL = 0 := by
      have : (1 - P.δ) * ((piR P.VH qH - TH) - 2 * (piR P.VL qL - TL) - gap P qL) = 0 := by
        simp only [gap]; linear_combination e2 - e1
      exact (mul_eq_zero.mp this).resolve_left hd
    have e4 : (1 + P.δ * P.p) * (piR P.VL qL - TL) =
        - (P.δ * P.p) * (gap P qL - gap P (qSL P)) := by
      linear_combination e1 - P.δ * P.p * e3
    have hTL : TL = TeL P qL := by
      simp only [TeL]
      field_simp
      linear_combination -e4
    refine ⟨hTL, ?_⟩
    simp only [TeH]
    rw [hTL] at e3
    simp only [TeL] at e3
    field_simp at e3 ⊢
    linear_combination -e3
  · subst h1 h2
    simp only [cont, punish, retailerProfit, staticRent, TeL, TeH, gap]
    constructor
    · field_simp; ring
    · field_simp; ring
  · simp only [mfrProfit, TeL, TeH]
    field_simp
    ring
