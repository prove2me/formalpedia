-- Prove2me | solution 1 for SalesTrust.Sharing.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:23:34.739758+00:00
-- url     : https://prove2.me/submissions/5850fc5c-3dc6-4358-b4c1-457766654c49

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

open SalesTrust.Sharing

namespace STProp1

lemma mfr_eq (P : Params) (m : Menu) :
    mfrProfit P m = P.p * piR P.VH m.qH + (1 - P.p) * piR P.VL m.qL - retailerProfit P m := by
  simp only [mfrProfit, retailerProfit]; ring

lemma gap_eq (P : Params) (q : ℝ) : gap P q = (P.VH - P.VL) * q := by
  simp only [gap, piR]; ring

lemma piRH (P : Params) (q : ℝ) : piR P.VH q = piR P.VL q + (P.VH - P.VL) * q := by
  simp only [piR]; ring

/-- Lower bound on the retailer's profit in the no-sharing program, from `IR^D_L` and `IC^S_H`. -/
lemma rbound (P : Params) (hS : P.Standing) (m : Menu) (h : FeasibleNE P m) :
    P.δ * staticRent P + (1 - P.δ) * P.p * (P.VH - P.VL) * m.qL +
      ((1 - P.δ) * (P.p * ((piR P.VH m.qH - m.TH) - (piR P.VL m.qL - m.TL)
        - (P.VH - P.VL) * m.qL)) +
       ((1 - P.δ) * (piR P.VL m.qL - m.TL) + P.δ * retailerProfit P m - P.δ * staticRent P))
      = retailerProfit P m ∧
    0 ≤ P.p * ((piR P.VH m.qH - m.TH) - (piR P.VL m.qL - m.TL) - (P.VH - P.VL) * m.qL) ∧
    0 ≤ (1 - P.δ) * (piR P.VL m.qL - m.TL) + P.δ * retailerProfit P m - P.δ * staticRent P := by
  obtain ⟨hp0, hp1, hV, -, hd0, hd1⟩ := hS
  obtain ⟨-, ⟨-, hIRL⟩, ⟨hICH, -⟩⟩ := h
  have hd : 0 < 1 - P.δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [retailerProfit]; ring
  · apply mul_nonneg hp0.le
    rw [piRH P m.qL] at hICH; linarith
  · simp only [cont, punish] at hIRL
    have := mul_le_mul_of_nonneg_left hIRL hd.le
    have e1 : (1 - P.δ) * (P.δ / (1 - P.δ) * staticRent P) = P.δ * staticRent P := by
      field_simp
    have e2 : (1 - P.δ) * (piR P.VL m.qL - m.TL + P.δ / (1 - P.δ) * retailerProfit P m)
        = (1 - P.δ) * (piR P.VL m.qL - m.TL) + P.δ * retailerProfit P m := by
      field_simp
    linarith

/-- the optimal low quantity -/
lemma G_eq (P : Params) (hS : P.Standing) (qH qL : ℝ) :
    P.p * piR P.VH qH + (1 - P.p) * piR P.VL qL - (1 - P.δ) * P.p * (P.VH - P.VL) * qL =
      (P.p * piR P.VH (menuNE P).qH + (1 - P.p) * piR P.VL (menuNE P).qL
        - (1 - P.δ) * P.p * (P.VH - P.VL) * (menuNE P).qL)
      - P.p * (qH - (menuNE P).qH) ^ 2 - (1 - P.p) * (qL - (menuNE P).qL) ^ 2 := by
  obtain ⟨hp0, hp1, -, -, -, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  simp only [menuNE, piR, qSL]
  field_simp
  ring

lemma N1 (P : Params) (hS : P.Standing) :
    retailerProfit P (menuNE P) =
      P.δ * staticRent P + (1 - P.δ) * P.p * (P.VH - P.VL) * (menuNE P).qL := by
  obtain ⟨hp0, hp1, -, -, -, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  simp only [retailerProfit, staticRent, gap, menuNE, piR, qSL, TSH, TSL]
  field_simp
  ring

lemma N2 (P : Params) (hS : P.Standing) :
    (piR P.VH (menuNE P).qH - (menuNE P).TH) - (piR P.VL (menuNE P).qL - (menuNE P).TL)
      = (P.VH - P.VL) * (menuNE P).qL := by
  obtain ⟨hp0, hp1, -, -, -, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  simp only [menuNE, piR, qSL, TSH, TSL]
  field_simp
  ring

lemma qLpos (P : Params) (hS : P.Standing) : 0 < (menuNE P).qL ∧ (menuNE P).qL < (menuNE P).qH := by
  obtain ⟨hp0, hp1, hV, hpV, hd0, hd1⟩ := hS
  have h1 : 0 < 1 - P.p := by linarith
  have e : (menuNE P).qL = (P.VL - P.p * P.VH + P.δ * P.p * (P.VH - P.VL)) / (2 * (1 - P.p)) := by
    simp only [menuNE, qSL]; field_simp; ring
  have e2 : (menuNE P).qH = P.VH / 2 := rfl
  rw [e, e2]
  constructor
  · apply div_pos _ (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hd0 hp0.le) (sub_nonneg.mpr hV.le)]
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_pos (sub_pos.mpr hd1) (mul_pos hp0 (sub_pos.mpr hV))]

end STProp1

open STProp1 in
theorem solution (P : Params) (hS : P.Standing) :
    IsOptimalNE P (menuNE P) ∧ ∀ m, IsOptimalNE P m → m = menuNE P := by
  have hS' := hS
  obtain ⟨hp0, hp1, hV, hpV, hd0, hd1⟩ := hS'
  have hd : 0 < 1 - P.δ := by linarith
  have hD : 0 < P.VH - P.VL := by linarith
  obtain ⟨hq0, hq1⟩ := qLpos P hS
  have hN1 := N1 P hS
  have hN2 := N2 P hS
  -- feasibility of menuNE
  have hfeas : FeasibleNE P (menuNE P) := by
    have hqH : (menuNE P).qH = P.VH / 2 := rfl
    -- IR^D_L with equality, in scaled form
    have hR : retailerProfit P (menuNE P) = (piR P.VL (menuNE P).qL - (menuNE P).TL)
        + P.p * (P.VH - P.VL) * (menuNE P).qL := by
      simp only [retailerProfit] at *; linear_combination P.p * hN2
    have hc : P.δ / (1 - P.δ) * (1 - P.δ) = P.δ := by field_simp
    have hIRL : punish P = piR P.VL (menuNE P).qL - (menuNE P).TL + cont P (menuNE P) := by
      simp only [punish, cont]
      have : P.δ / (1 - P.δ) * staticRent P - P.δ / (1 - P.δ) * retailerProfit P (menuNE P)
          = (piR P.VL (menuNE P).qL - (menuNE P).TL) := by
        have e : P.δ / (1 - P.δ) * staticRent P - P.δ / (1 - P.δ) * retailerProfit P (menuNE P)
            = P.δ / (1 - P.δ) * (staticRent P - retailerProfit P (menuNE P)) := by ring
        rw [e]
        have e3 : staticRent P - retailerProfit P (menuNE P) =
            (1 - P.δ) * (staticRent P - P.p * (P.VH - P.VL) * (menuNE P).qL) := by
          rw [hN1]; ring
        rw [e3]
        have e4 : piR P.VL (menuNE P).qL - (menuNE P).TL =
            P.δ * (staticRent P - P.p * (P.VH - P.VL) * (menuNE P).qL) := by
          linear_combination (hR.symm.trans hN1)
        rw [e4]
        field_simp
      linarith
    refine ⟨⟨by rw [hqH]; linarith, hq0.le⟩, ⟨?_, hIRL.le⟩, ⟨?_, ?_⟩⟩
    · rw [hIRL]
      have : 0 ≤ (P.VH - P.VL) * (menuNE P).qL := mul_nonneg hD.le hq0.le
      linarith
    · rw [piRH P (menuNE P).qL]; linarith
    · rw [piRH P (menuNE P).qH] at hN2
      have : (P.VH - P.VL) * (menuNE P).qL ≤ (P.VH - P.VL) * (menuNE P).qH :=
        mul_le_mul_of_nonneg_left hq1.le hD.le
      linarith
  -- upper bound for any feasible menu
  have hub : ∀ m, FeasibleNE P m → mfrProfit P m ≤ mfrProfit P (menuNE P) -
      P.p * (m.qH - (menuNE P).qH) ^ 2 - (1 - P.p) * (m.qL - (menuNE P).qL) ^ 2 := by
    intro m hm
    obtain ⟨hdec, ha, hb⟩ := rbound P hS m hm
    have hG := G_eq P hS m.qH m.qL
    rw [mfr_eq, mfr_eq, hN1]
    have : 0 ≤ (1 - P.δ) * (P.p * ((piR P.VH m.qH - m.TH) - (piR P.VL m.qL - m.TL)
        - (P.VH - P.VL) * m.qL)) := mul_nonneg hd.le ha
    linarith
  refine ⟨⟨hfeas, fun m' hm' => ?_⟩, fun m hm => ?_⟩
  · have := hub m' hm'
    nlinarith [sq_nonneg (m'.qH - (menuNE P).qH), sq_nonneg (m'.qL - (menuNE P).qL)]
  · obtain ⟨hmF, hmax⟩ := hm
    have h1 := hmax _ hfeas
    have h2 := hub m hmF
    have s1 : P.p * (m.qH - (menuNE P).qH) ^ 2 = 0 := by
      nlinarith [sq_nonneg (m.qH - (menuNE P).qH), sq_nonneg (m.qL - (menuNE P).qL)]
    have s2 : (1 - P.p) * (m.qL - (menuNE P).qL) ^ 2 = 0 := by
      nlinarith [sq_nonneg (m.qH - (menuNE P).qH), sq_nonneg (m.qL - (menuNE P).qL)]
    have eqH : m.qH = (menuNE P).qH := by
      have := (mul_eq_zero.mp s1).resolve_left hp0.ne'
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    have eqL : m.qL = (menuNE P).qL := by
      have := (mul_eq_zero.mp s2).resolve_left (by linarith)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    -- slacks vanish
    obtain ⟨hdec, ha, hb⟩ := rbound P hS m hmF
    have hpH : piR P.VH m.qH = piR P.VH (menuNE P).qH := by rw [eqH]
    have hpL : piR P.VL m.qL = piR P.VL (menuNE P).qL := by rw [eqL]
    have hX : (P.VH - P.VL) * m.qL = (P.VH - P.VL) * (menuNE P).qL := by rw [eqL]
    have hRm : retailerProfit P m = retailerProfit P (menuNE P) := by
      have e1 := mfr_eq P m
      have e2 := mfr_eq P (menuNE P)
      nlinarith [sq_nonneg (m.qH - (menuNE P).qH), sq_nonneg (m.qL - (menuNE P).qL)]
    have ha' : 0 ≤ (1 - P.δ) * (P.p * ((piR P.VH m.qH - m.TH) - (piR P.VL m.qL - m.TL)
        - (P.VH - P.VL) * m.qL)) := mul_nonneg hd.le ha
    have hsum : (1 - P.δ) * (P.p * ((piR P.VH m.qH - m.TH) - (piR P.VL m.qL - m.TL)
        - (P.VH - P.VL) * m.qL)) + ((1 - P.δ) * (piR P.VL m.qL - m.TL) + P.δ * retailerProfit P m
          - P.δ * staticRent P) = 0 := by
      linear_combination hdec + hRm + hN1 - (1 - P.δ) * P.p * hX
    have hs1 : (1 - P.δ) * (P.p * ((piR P.VH m.qH - m.TH) - (piR P.VL m.qL - m.TL)
        - (P.VH - P.VL) * m.qL)) = 0 := by linarith
    have hs2 : (1 - P.δ) * (piR P.VL m.qL - m.TL) + P.δ * retailerProfit P m
          - P.δ * staticRent P = 0 := by linarith
    have hICe : (piR P.VH m.qH - m.TH) - (piR P.VL m.qL - m.TL) - (P.VH - P.VL) * m.qL = 0 := by
      have := (mul_eq_zero.mp hs1).resolve_left hd.ne'
      exact (mul_eq_zero.mp this).resolve_left hp0.ne'
    have hR : retailerProfit P (menuNE P) = (piR P.VL (menuNE P).qL - (menuNE P).TL)
        + P.p * (P.VH - P.VL) * (menuNE P).qL := by
      simp only [retailerProfit]; linear_combination P.p * hN2
    have hsN : (1 - P.δ) * (piR P.VL (menuNE P).qL - (menuNE P).TL)
        + P.δ * retailerProfit P (menuNE P) - P.δ * staticRent P = 0 := by
      have e4 : piR P.VL (menuNE P).qL - (menuNE P).TL =
          P.δ * (staticRent P - P.p * (P.VH - P.VL) * (menuNE P).qL) := by
        linear_combination (hR.symm.trans hN1)
      rw [e4, hN1]; ring
    have hTL : m.TL = (menuNE P).TL := by
      have : (1 - P.δ) * (m.TL - (menuNE P).TL) = 0 := by
        linear_combination hsN - hs2 + P.δ * hRm + (1 - P.δ) * hpL
      have := (mul_eq_zero.mp this).resolve_left hd.ne'
      linarith
    have hTH : m.TH = (menuNE P).TH := by
      linear_combination -hICe + hN2 + hpH - hpL + hTL - hX
    exact Menu.ext eqH hTH eqL hTL
