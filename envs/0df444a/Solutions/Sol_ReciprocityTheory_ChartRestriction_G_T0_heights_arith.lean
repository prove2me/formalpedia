-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.heights_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:37.926885+00:00
-- url     : https://prove2.me/submissions/65660a6e-2024-414d-a7c5-e35956235371

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtArith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution
    (D δ L lr lw1 hN sF laW nuS c g0 i DF PP0' PN tableLineDegreeFive tableLineDegreeTwo PI4 Prw G Pet
      aL ade aG1 aF aG2 HMM HL Hde HF SI SN Ssum δlogδ : ℝ)
    (hD : 3 ≤ D) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcg : c * g0 ≤ 1 / 2)
    (hg0 : 0 ≤ g0) (hi : 1 ≤ i)
    (hP : 1 ≤ PP0' ∧ 1 ≤ PN ∧ 1 ≤ tableLineDegreeFive ∧ 1 ≤ tableLineDegreeTwo ∧ 1 ≤ PI4 ∧ 1 ≤ Prw ∧ 1 ≤ G ∧ 1 ≤ Pet)
    (hlr0 : 0 ≤ lr) (hlr : lr ≤ Prw * L) (hlw1 : lw1 ≤ Prw * L) (hhN : hN / 2 ≤ Prw * L)
    (hDF : DF ≤ L) (hlaW : laW ≤ G * L) (hnu : nuS ≤ PN * L)

    (hUP : sF ≤ (D + 2) * δ * (PP0' * L + max 0 laW + lw1))
    (hb1 : HMM = sF + δ * hN / 2)

    (haL : aL ≤ 4 / 3 * δ) (hade0 : 0 ≤ ade) (hade : ade ≤ aL) (haG10 : 0 ≤ aG1) (haG1 : aG1 ≤ aL)
    (haF0 : 0 ≤ aF) (haF : aF ≤ (D + 4) * aL) (haG20 : 0 ≤ aG2) (haG2 : aG2 ≤ (D + 4) * aL)

    (h7a : HL ≤ HMM + δ * (nuS + tableLineDegreeFive * DF + c * tableLineDegreeTwo) + D * c * g0 * ade * lr + c * g0 * Hde)
    (h7b : Hde ≤ HL + (δ * PI4 * D * L + D * aG1 * lr))
    (h7c : HF ≤ (D + 4) * HL + δ * PI4 * D * L + D * aG2 * lr)

    (hdi : 2 * SI ≤ δlogδ + 2 * Ssum + 2 * D * aF * lr + 2 * HF)
    (hdn : SN / i ≤ g0 * (Hde + D * ade * lr) + δ * Pet) :
    let PH := PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw
    2 * SI ≤ δlogδ + 2 * Ssum + 8 / 3 * D * (D + 4) * δ * Prw * L +
        2 * (D + 4) * (D + 1) * δ * (2 * G + 6 * (2 * PH + G)) * L ∧
      SN / i ≤ g0 * ((D + 1) * δ * (2 * G + 6 * (2 * PH + G)) * L + 4 / 3 * D * δ * Prw * L) +
        δ * Pet := by
  dsimp only
  obtain ⟨hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8⟩ := hP
  have hD0 : 0 ≤ D := by linarith
  have hD4 : 0 ≤ D + 4 := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hT : 0 ≤ δ * L := mul_nonneg hδ hL0
  have hcg0 : 0 ≤ c * g0 := mul_nonneg hc0 hg0
  have haL' : ade ≤ 4 / 3 * δ := hade.trans haL
  have hPL : 0 ≤ Prw * L := mul_nonneg (by linarith) hL0
  have hδPL : 0 ≤ 4 / 3 * δ * (Prw * L) := mul_nonneg (by linarith) hPL
  have hmax : max 0 laW ≤ G * L := max_le (mul_nonneg (by linarith) hL0) hlaW
  have hin : PP0' * L + max 0 laW + lw1 ≤ (PP0' + G + Prw) * L := by linarith
  have hsF : sF ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) :=
    hUP.trans (mul_le_mul_of_nonneg_left hin (mul_nonneg (by linarith) hδ))
  have hN2 : δ * hN / 2 ≤ δ * (Prw * L) := by
    have := mul_le_mul_of_nonneg_left hhN hδ
    linarith
  have hnu2 : δ * (nuS + tableLineDegreeFive * DF + c * tableLineDegreeTwo) ≤ δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) := by
    apply mul_le_mul_of_nonneg_left _ hδ
    have h1 : tableLineDegreeFive * DF ≤ tableLineDegreeFive * L := mul_le_mul_of_nonneg_left hDF (by linarith)
    have h2 : c * tableLineDegreeTwo ≤ 1 * tableLineDegreeTwo := mul_le_mul_of_nonneg_right hc1 (by linarith)
    have h3 : tableLineDegreeTwo * 1 ≤ tableLineDegreeTwo * L := mul_le_mul_of_nonneg_left hL (by linarith)
    linarith
  have hcross : D * c * g0 * ade * lr ≤ D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := by
    have h1 : ade * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul haL' hlr hlr0 (by linarith)
    have h2 : c * g0 * (ade * lr) ≤ 1 / 2 * (4 / 3 * δ * (Prw * L)) :=
      mul_le_mul hcg h1 (mul_nonneg hade0 hlr0) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left h2 hD0
    linarith
  have hadl : D * ade * lr ≤ D * (4 / 3 * δ * (Prw * L)) := by
    have h1 : ade * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul haL' hlr hlr0 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hY1 : D * aG1 * lr ≤ D * (4 / 3 * δ * (Prw * L)) := by
    have h1 : aG1 * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul (haG1.trans haL) hlr hlr0 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hA4 : (D + 4) * aL ≤ (D + 4) * (4 / 3 * δ) := mul_le_mul_of_nonneg_left haL hD4
  have hY2 : D * aG2 * lr ≤ D * ((D + 4) * (4 / 3 * δ) * (Prw * L)) := by
    have h1 : aG2 * lr ≤ (D + 4) * (4 / 3 * δ) * (Prw * L) :=
      mul_le_mul (haG2.trans hA4) hlr hlr0 (mul_nonneg hD4 (by linarith))
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hYF : D * aF * lr ≤ D * ((D + 4) * (4 / 3 * δ) * (Prw * L)) := by
    have h1 : aF * lr ≤ (D + 4) * (4 / 3 * δ) * (Prw * L) :=
      mul_le_mul (haF.trans hA4) hlr hlr0 (mul_nonneg hD4 (by linarith))
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hPI : 0 ≤ δ * PI4 * D * L :=
    mul_nonneg (mul_nonneg (mul_nonneg hδ (by linarith)) hD0) hL0
  have hXb0 : 0 ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := by
    have e1 : 0 ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) :=
      mul_nonneg (mul_nonneg (by linarith) hδ) (mul_nonneg (by linarith) hL0)
    have e2 : 0 ≤ δ * (Prw * L) := mul_nonneg hδ hPL
    have e3 : 0 ≤ δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) := mul_nonneg hδ (mul_nonneg (by linarith) hL0)
    have e4 : 0 ≤ D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := mul_nonneg hD0 (by linarith)
    linarith
  have hYb0 : 0 ≤ δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)) := by
    have := mul_nonneg hD0 hδPL
    linarith
  have hHde : Hde ≤ HL + (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L))) := by linarith
  have hHL1 : HL ≤ ((D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L)))) +
      c * g0 * (HL + (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)))) := by
    have := mul_le_mul_of_nonneg_left hHde hcg0
    linarith
  have hHL : HL ≤ 2 * ((D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L)))) +
      (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L))) := by
    by_cases hHL0 : 0 ≤ HL
    · have a1 := mul_le_mul_of_nonneg_right hcg hHL0
      have a2 := mul_le_mul_of_nonneg_right hcg hYb0
      linarith
    · push_neg at hHL0
      linarith
  have hHF := mul_le_mul_of_nonneg_left hHL hD4
  have e1 : 0 ≤ (D + 4) * (6 * D + 4) * G := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e2 : 0 ≤ (D + 4) * (10 * D + 8) * PP0' := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e3 : 0 ≤ (D + 4) * (6 * D + 6) * Prw := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e4 : 0 ≤ (D + 4) * (12 * D + 10) * (PN + tableLineDegreeFive + tableLineDegreeTwo) :=
    mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e5 : 0 ≤ (11 * D * D + 55 * D + 48) * PI4 := mul_nonneg (by nlinarith) (by linarith)
  have hE := mul_nonneg hT (add_nonneg (add_nonneg (add_nonneg (add_nonneg e1 e2) e3) e4) e5)
  have f1 : 0 ≤ (6 * D + 4) * G := mul_nonneg (by linarith) (by linarith)
  have f2 : 0 ≤ (10 * D + 8) * PP0' := mul_nonneg (by linarith) (by linarith)
  have f3 : 0 ≤ (12 * D + 10) * (PN + tableLineDegreeFive + tableLineDegreeTwo) := mul_nonneg (by linarith) (by linarith)
  have f4 : 0 ≤ (10 * D + 12) * PI4 := mul_nonneg (by linarith) (by linarith)
  have f5 : 0 ≤ (6 * D + 6) * Prw := mul_nonneg (by linarith) (by linarith)
  have hE2 := mul_nonneg hT (add_nonneg (add_nonneg (add_nonneg (add_nonneg f1 f2) f3) f4) f5)
  constructor
  · linarith
  · have hb : Hde + D * ade * lr ≤ (D + 1) * δ * (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L +
        4 / 3 * D * δ * Prw * L := by linarith
    have := mul_le_mul_of_nonneg_left hb hg0
    linarith
end ReciprocityTheory.ChartRestriction.G.T0
