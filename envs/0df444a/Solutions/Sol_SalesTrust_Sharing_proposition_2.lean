-- Prove2me | solution 1 for SalesTrust.Sharing.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:27:05.145131+00:00
-- url     : https://prove2.me/submissions/b09c9b4a-c85a-441f-8b29-a9790b832511

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

open SalesTrust.Sharing

namespace STProp2

lemma mfr_eq (P : Params) (m : Menu) :
    mfrProfit P m = P.p * piR P.VH m.qH + (1 - P.p) * piR P.VL m.qL - retailerProfit P m := by
  simp only [mfrProfit, retailerProfit]; ring

lemma piRH (P : Params) (q : ℝ) : piR P.VH q = piR P.VL q + (P.VH - P.VL) * q := by
  simp only [piR]; ring

/-- scaled slack of `IC^D_H` -/
noncomputable def slA (P : Params) (m : Menu) : ℝ :=
  (1 - P.δ) * ((piR P.VH m.qH - m.TH) - (piR P.VL m.qL - m.TL) - (P.VH - P.VL) * m.qL)
    + P.δ * retailerProfit P m - P.δ * staticRent P

/-- scaled slack of `IR^D_L` -/
noncomputable def slB (P : Params) (m : Menu) : ℝ :=
  (1 - P.δ) * (piR P.VL m.qL - m.TL) + P.δ * retailerProfit P m - P.δ * staticRent P

lemma decomp (P : Params) (m : Menu) :
    (1 + P.δ * P.p) * retailerProfit P m =
      (1 + P.p) * P.δ * staticRent P + (1 - P.δ) * P.p * (P.VH - P.VL) * m.qL
        + P.p * slA P m + slB P m := by
  simp only [slA, slB, retailerProfit]; ring

lemma slacks_nonneg (P : Params) (hS : P.Standing) (m : Menu) (h : FeasibleE P m) :
    0 ≤ slA P m ∧ 0 ≤ slB P m := by
  obtain ⟨hp0, hp1, hV, -, hd0, hd1⟩ := hS
  obtain ⟨-, ⟨-, hIRL⟩, ⟨hICH, -⟩⟩ := h
  have hd : 0 < 1 - P.δ := by linarith
  simp only [cont, punish] at hIRL hICH
  have e1 : (1 - P.δ) * (P.δ / (1 - P.δ) * staticRent P) = P.δ * staticRent P := by
    field_simp
  have e2 : (1 - P.δ) * (P.δ / (1 - P.δ) * retailerProfit P m) = P.δ * retailerProfit P m := by
    field_simp
  constructor
  · have := mul_le_mul_of_nonneg_left hICH hd.le
    rw [piRH P m.qL] at this
    simp only [slA]
    nlinarith
  · have := mul_le_mul_of_nonneg_left hIRL hd.le
    simp only [slB]
    nlinarith

lemma G_eq (P : Params) (hS : P.Standing) (qH qL : ℝ) :
    (1 + P.δ * P.p) * (P.p * piR P.VH qH + (1 - P.p) * piR P.VL qL)
        - (1 - P.δ) * P.p * (P.VH - P.VL) * qL =
      ((1 + P.δ * P.p) * (P.p * piR P.VH (menuE P).qH + (1 - P.p) * piR P.VL (menuE P).qL)
        - (1 - P.δ) * P.p * (P.VH - P.VL) * (menuE P).qL)
      - (1 + P.δ * P.p) * P.p * (qH - (menuE P).qH) ^ 2
      - (1 + P.δ * P.p) * (1 - P.p) * (qL - (menuE P).qL) ^ 2 := by
  obtain ⟨hp0, hp1, -, -, hd0, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  have h2 : (1 + P.δ * P.p) ≠ 0 := by nlinarith
  simp only [menuE, piR, qSL]
  field_simp
  ring

lemma slB_E (P : Params) (hS : P.Standing) : slB P (menuE P) = 0 := by
  obtain ⟨hp0, hp1, -, -, hd0, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  have h2 : (1 + P.δ * P.p) ≠ 0 := by nlinarith
  simp only [slB, retailerProfit, staticRent, gap, menuE, piR, qSL, TSH, TSL]
  field_simp
  ring

lemma slA_E (P : Params) (hS : P.Standing) : slA P (menuE P) = 0 := by
  obtain ⟨hp0, hp1, -, -, hd0, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  have h2 : (1 + P.δ * P.p) ≠ 0 := by nlinarith
  simp only [slA, retailerProfit, staticRent, gap, menuE, piR, qSL, TSH, TSL]
  field_simp
  ring

lemma uL_E (P : Params) (hS : P.Standing) :
    (1 + P.δ * P.p) * (piR P.VL (menuE P).qL - (menuE P).TL) =
      P.δ * P.p * (P.VH - P.VL) * (qSL P - (menuE P).qL) := by
  obtain ⟨hp0, hp1, -, -, hd0, -⟩ := hS
  have h1 : (1 - P.p) ≠ 0 := by linarith
  have h2 : (1 + P.δ * P.p) ≠ 0 := by nlinarith
  simp only [menuE, piR, qSL, TSH, TSL]
  field_simp
  ring

lemma qL_E (P : Params) (hS : P.Standing) :
    0 < qSL P ∧ qSL P ≤ (menuE P).qL ∧ (menuE P).qL < (menuE P).qH := by
  obtain ⟨hp0, hp1, hV, hpV, hd0, hd1⟩ := hS
  have h1 : 0 < 1 - P.p := by linarith
  have h2 : 0 < 1 + P.δ * P.p := by nlinarith
  have eS : qSL P = (P.VL - P.p * P.VH) / (2 * (1 - P.p)) := by
    simp only [qSL]; field_simp; ring
  have e : (menuE P).qL = qSL P + (1 + P.p) * (P.δ * P.p) * (P.VH - P.VL) /
      (2 * (1 + P.δ * P.p) * (1 - P.p)) := by
    simp only [menuE]; field_simp
  have e' : (menuE P).qL = P.VL / 2 - (1 - P.δ) * P.p * (P.VH - P.VL) /
      (2 * (1 + P.δ * P.p) * (1 - P.p)) := by
    simp only [menuE, qSL]; field_simp; ring
  have e2 : (menuE P).qH = P.VH / 2 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eS]; apply div_pos (by linarith) (by linarith)
  · rw [e]
    have : 0 ≤ (1 + P.p) * (P.δ * P.p) * (P.VH - P.VL) / (2 * (1 + P.δ * P.p) * (1 - P.p)) := by
      apply div_nonneg
      · apply mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hd0 hp0.le)) (by linarith)
      · positivity
    linarith
  · rw [e', e2]
    have : 0 ≤ (1 - P.δ) * P.p * (P.VH - P.VL) / (2 * (1 + P.δ * P.p) * (1 - P.p)) := by
      apply div_nonneg
      · apply mul_nonneg (mul_nonneg (by linarith) hp0.le) (by linarith)
      · positivity
    linarith

end STProp2

open STProp2 in
theorem solution (P : Params) (hS : P.Standing) :
    IsOptimalE P (menuE P) ∧ ∀ m, IsOptimalE P m → m = menuE P := by
  have hS' := hS
  obtain ⟨hp0, hp1, hV, hpV, hd0, hd1⟩ := hS'
  have hd : 0 < 1 - P.δ := by linarith
  have hD : 0 < P.VH - P.VL := by linarith
  have hk : 0 < 1 + P.δ * P.p := by nlinarith
  obtain ⟨hs0, hsq, hq1⟩ := qL_E P hS
  have hq0 : 0 < (menuE P).qL := lt_of_lt_of_le hs0 hsq
  have hA := slA_E P hS
  have hB := slB_E P hS
  have hu := uL_E P hS
  -- feasibility of menuE
  have hfeas : FeasibleE P (menuE P) := by
    have hqH : (menuE P).qH = P.VH / 2 := rfl
    set uL := piR P.VL (menuE P).qL - (menuE P).TL with huL
    set uH := piR P.VH (menuE P).qH - (menuE P).TH with huH
    set X := punish P with hX
    set Y := cont P (menuE P) with hY
    have hc : X - Y = (P.δ / (1 - P.δ)) * (staticRent P - retailerProfit P (menuE P)) := by
      rw [hX, hY]; simp only [punish, cont]; ring
    have hBu : (1 - P.δ) * uL = P.δ * (staticRent P - retailerProfit P (menuE P)) := by
      simp only [slB] at hB; linear_combination hB
    have hAu : (1 - P.δ) * (uH - uL - (P.VH - P.VL) * (menuE P).qL)
        = P.δ * (staticRent P - retailerProfit P (menuE P)) := by
      simp only [slA] at hA; linear_combination hA
    have hXY : X - Y = uL := by
      rw [hc]
      have : uL = P.δ * (staticRent P - retailerProfit P (menuE P)) / (1 - P.δ) := by
        rw [← hBu]; field_simp
      rw [this]; field_simp
    have hH : uH - uL - (P.VH - P.VL) * (menuE P).qL = uL := by
      have : (1 - P.δ) * (uH - uL - (P.VH - P.VL) * (menuE P).qL - uL) = 0 := by
        linear_combination hAu - hBu
      have := (mul_eq_zero.mp this).resolve_left hd.ne'
      linarith
    have huneg : uL ≤ 0 := by
      have : (1 + P.δ * P.p) * uL ≤ 0 := by
        rw [hu]
        apply mul_nonpos_of_nonneg_of_nonpos
        · exact mul_nonneg (mul_nonneg hd0 hp0.le) hD.le
        · linarith
      nlinarith
    have hupos : 0 ≤ uL + (P.VH - P.VL) * (menuE P).qL := by
      have : 0 ≤ (1 + P.δ * P.p) * (uL + (P.VH - P.VL) * (menuE P).qL) := by
        have e : (1 + P.δ * P.p) * (uL + (P.VH - P.VL) * (menuE P).qL) =
            (P.VH - P.VL) * ((menuE P).qL + P.δ * P.p * qSL P) := by
          linear_combination hu
        rw [e]
        apply mul_nonneg hD.le
        have := mul_nonneg (mul_nonneg hd0 hp0.le) hs0.le
        linarith
      nlinarith
    have hDq : (P.VH - P.VL) * (menuE P).qL ≤ (P.VH - P.VL) * (menuE P).qH :=
      mul_le_mul_of_nonneg_left hq1.le hD.le
    refine ⟨⟨by rw [hqH]; linarith, hq0.le⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · show X ≤ uH + Y
      linarith
    · show X ≤ uL + Y
      linarith
    · show piR P.VH (menuE P).qL - (menuE P).TL + X ≤ uH + Y
      rw [piRH P (menuE P).qL]
      linarith
    · show piR P.VL (menuE P).qH - (menuE P).TH + X ≤ uL + Y
      have : piR P.VL (menuE P).qH - (menuE P).TH = uH - (P.VH - P.VL) * (menuE P).qH := by
        rw [huH, piRH P (menuE P).qH]; ring
      rw [this]
      linarith
  -- master identity for any menu
  have hkey : ∀ m : Menu, (1 + P.δ * P.p) * mfrProfit P m
      + (1 + P.δ * P.p) * P.p * (m.qH - (menuE P).qH) ^ 2
      + (1 + P.δ * P.p) * (1 - P.p) * (m.qL - (menuE P).qL) ^ 2
      + (P.p * slA P m + slB P m) = (1 + P.δ * P.p) * mfrProfit P (menuE P) := by
    intro m
    have hG := G_eq P hS m.qH m.qL
    have d1 := decomp P m
    have d2 := decomp P (menuE P)
    rw [mfr_eq, mfr_eq]
    rw [hA, hB] at d2
    linear_combination hG + d2 - d1
  refine ⟨⟨hfeas, fun m' hm' => ?_⟩, fun m hm => ?_⟩
  · obtain ⟨ha, hb⟩ := slacks_nonneg P hS m' hm'
    have := hkey m'
    have : 0 ≤ (1 + P.δ * P.p) * P.p * (m'.qH - (menuE P).qH) ^ 2 :=
      mul_nonneg (mul_nonneg hk.le hp0.le) (sq_nonneg _)
    have : 0 ≤ (1 + P.δ * P.p) * (1 - P.p) * (m'.qL - (menuE P).qL) ^ 2 :=
      mul_nonneg (mul_nonneg hk.le (by linarith)) (sq_nonneg _)
    have : 0 ≤ P.p * slA P m' := mul_nonneg hp0.le ha
    have : (1 + P.δ * P.p) * mfrProfit P m' ≤ (1 + P.δ * P.p) * mfrProfit P (menuE P) := by
      linarith
    exact le_of_mul_le_mul_left this hk
  · obtain ⟨hmF, hmax⟩ := hm
    have h1 := hmax _ hfeas
    obtain ⟨ha, hb⟩ := slacks_nonneg P hS m hmF
    have hm' := hkey m
    have t1 : 0 ≤ (1 + P.δ * P.p) * P.p * (m.qH - (menuE P).qH) ^ 2 :=
      mul_nonneg (mul_nonneg hk.le hp0.le) (sq_nonneg _)
    have t2 : 0 ≤ (1 + P.δ * P.p) * (1 - P.p) * (m.qL - (menuE P).qL) ^ 2 :=
      mul_nonneg (mul_nonneg hk.le (by linarith)) (sq_nonneg _)
    have t3 : 0 ≤ P.p * slA P m := mul_nonneg hp0.le ha
    have t4 : (1 + P.δ * P.p) * mfrProfit P (menuE P) ≤ (1 + P.δ * P.p) * mfrProfit P m :=
      mul_le_mul_of_nonneg_left h1 hk.le
    have z1 : (1 + P.δ * P.p) * P.p * (m.qH - (menuE P).qH) ^ 2 = 0 := by linarith
    have z2 : (1 + P.δ * P.p) * (1 - P.p) * (m.qL - (menuE P).qL) ^ 2 = 0 := by linarith
    have z3 : P.p * slA P m = 0 := by linarith
    have z4 : slB P m = 0 := by linarith
    have eqH : m.qH = (menuE P).qH := by
      have := (mul_eq_zero.mp z1).resolve_left (mul_pos hk hp0).ne'
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    have eqL : m.qL = (menuE P).qL := by
      have := (mul_eq_zero.mp z2).resolve_left (mul_pos hk (by linarith)).ne'
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    have z3' : slA P m = 0 := (mul_eq_zero.mp z3).resolve_left hp0.ne'
    have hpH : piR P.VH m.qH = piR P.VH (menuE P).qH := by rw [eqH]
    have hpL : piR P.VL m.qL = piR P.VL (menuE P).qL := by rw [eqL]
    have hX : (P.VH - P.VL) * m.qL = (P.VH - P.VL) * (menuE P).qL := by rw [eqL]
    have hRm : retailerProfit P m = retailerProfit P (menuE P) := by
      have d1 := decomp P m
      have d2 := decomp P (menuE P)
      rw [hA, hB, z4] at *
      have : (1 + P.δ * P.p) * (retailerProfit P m - retailerProfit P (menuE P)) = 0 := by
        linear_combination d1 - d2 + (1 - P.δ) * P.p * hX + P.p * z3'
      have := (mul_eq_zero.mp this).resolve_left hk.ne'
      linarith
    simp only [slB] at z4 hB
    simp only [slA] at z3' hA
    have hTL : m.TL = (menuE P).TL := by
      have : (1 - P.δ) * (m.TL - (menuE P).TL) = 0 := by
        linear_combination hB - z4 + P.δ * hRm + (1 - P.δ) * hpL
      have := (mul_eq_zero.mp this).resolve_left hd.ne'
      linarith
    have hTH : m.TH = (menuE P).TH := by
      have : (1 - P.δ) * (m.TH - (menuE P).TH) = 0 := by
        linear_combination hA - z3' + P.δ * hRm + (1 - P.δ) * hpH - (1 - P.δ) * hpL
          + (1 - P.δ) * hTL - (1 - P.δ) * hX
      have := (mul_eq_zero.mp this).resolve_left hd.ne'
      linarith
    exact Menu.ext eqH hTH eqL hTL
