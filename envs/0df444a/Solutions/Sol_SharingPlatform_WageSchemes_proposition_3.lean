-- Prove2me | solution 1 for SharingPlatform.WageSchemes.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:24:38.944728+00:00
-- url     : https://prove2.me/submissions/c6e81439-fb52-4edb-88e6-312de131665b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model
import Theorems.Thm_SharingPlatform_WageSchemes_lemma_1
import Theorems.Thm_SharingPlatform_WageSchemes_lemma_2
import Theorems.Thm_SharingPlatform_WageSchemes_lemma_3
import Theorems.Thm_SharingPlatform_WageSchemes_profit_increasing_in_price
import Theorems.Thm_SharingPlatform_WageSchemes_price_dcr_vs_fw
import Theorems.Thm_SharingPlatform_WageSchemes_fcr_vs_dcr
import Theorems.Thm_SharingPlatform_WageSchemes_fcr_vs_fw

open SharingPlatform.WageSchemes

/-- Symmetric profit when demand equals supply and demand is positive. -/
private lemma profit_sym_eq (P : Params) (hm : P.m ≠ 0) (p w : ℝ)
    (h : P.a - P.c * p = -P.k + P.m * w) (hpos : 0 < P.a - P.c * p) :
    profit P p w p w = profitAtPrice P p := by
  have hd : demand P p p = P.a - P.c * p := by unfold demand; ring
  have hs : supply P w w = P.a - P.c * p := by unfold supply; rw [h]; ring
  have hw : w = (P.a - P.c * p + P.k) / P.m := by field_simp; linarith
  unfold profit volume profitAtPrice
  rw [hd, hs, min_self, max_eq_right hpos.le, hw]
  field_simp
  ring

theorem solution (P : Params) (hP : P.Standing)
    (xD : ℝ × ℝ) (hD : IsNashDCR P xD xD) (hDn : NontrivialDCR P xD xD)
    (eF : TwoStage) (hF : IsSPE P fcrWage eF) (hFc : eF.OnPathContinuous)
    (hFs : eF.IsSymmetric) (hFn : eF.Nontrivial P fcrWage)
    (eW : TwoStage) (hW : IsSPE P fwWage eW) (hWc : eW.OnPathContinuous)
    (hWs : eW.IsSymmetric) (hWn : eW.Nontrivial P fwWage) :
    (P.l / P.m < P.b / P.c →
      profitDCR P xD xD < eF.onPathProfit P fcrWage ∧
        eF.onPathProfit P fcrWage < eW.onPathProfit P fwWage) ∧
    (P.b / P.c < P.l / P.m → 0 < cond13 P xD.2 →
      eW.onPathProfit P fwWage < profitDCR P xD xD ∧
        profitDCR P xD xD < eF.onPathProfit P fcrWage) ∧
    (P.b / P.c < P.l / P.m → cond13 P xD.2 < 0 →
      eW.onPathProfit P fwWage < eF.onPathProfit P fcrWage ∧
        eF.onPathProfit P fcrWage < profitDCR P xD xD) := by
  obtain ⟨ha, hb, hc, hk, hl, hm, hA1, hA2⟩ := hP
  have hP' : P.Standing := ⟨ha, hb, hc, hk, hl, hm, hA1, hA2⟩
  have ham : 0 < P.a * P.m - P.c * P.k := by
    rw [div_lt_div_iff₀ hm hc] at hA1; linarith
  -- identify the three equilibria
  obtain ⟨-, -, hαD0, hαD1, huniq⟩ := lemma_1 P hP'
  have hxD : xD = (pD P, alphaD P) := huniq xD hD hDn
  obtain ⟨-, -, hFchar⟩ := lemma_2 P hP'
  obtain ⟨hαI, hf0, -, -, hpF⟩ := hFchar eF hF hFc hFs hFn
  obtain ⟨-, hWchar⟩ := lemma_3 P hP'
  obtain ⟨hxW, hpW⟩ := hWchar eW hW hWc hWs hWn
  obtain ⟨hmono, hpDh, hpWh, hpFh⟩ := profit_increasing_in_price P hP'
  set α := eF.x₁ with hαdef
  have hFh := hpFh α hαI hf0
  -- the on-path profits as functions of the price
  have hden : P.c * (P.b + P.c) * (P.l + 2 * P.m) + P.m * (P.b + 2 * P.c) * (P.l + P.m) ≠ 0 := by
    have : 0 < P.c * (P.b + P.c) * (P.l + 2 * P.m) + P.m * (P.b + 2 * P.c) * (P.l + P.m) := by
      have h1 : 0 < P.c * (P.b + P.c) * (P.l + 2 * P.m) := by
        apply mul_pos (mul_pos hc (by linarith)) (by linarith)
      have h2 : 0 < P.m * (P.b + 2 * P.c) * (P.l + P.m) := by
        apply mul_pos (mul_pos hm (by linarith)) (by linarith)
      linarith
    exact this.ne'
  have hNa : 0 < P.k * (P.b + P.c) * (P.l + P.m) +
      P.a * (P.m * (P.l + P.m) + (P.b + P.c) * (P.l + 2 * P.m)) := by
    have h1 : 0 < P.k * (P.b + P.c) * (P.l + P.m) :=
      mul_pos (mul_pos hk (by linarith)) (by linarith)
    have h2 : 0 < P.a * (P.m * (P.l + P.m) + (P.b + P.c) * (P.l + 2 * P.m)) := by
      apply mul_pos ha
      have : 0 < P.m * (P.l + P.m) := mul_pos hm (by linarith)
      have : 0 < (P.b + P.c) * (P.l + 2 * P.m) := mul_pos (by linarith) (by linarith)
      linarith
    linarith
  have hDid : P.a - P.c * pD P = -P.k + P.m * ((1 - alphaD P) * pD P) := by
    unfold pD alphaD
    field_simp
    ring
  have hDpos : 0 < P.a - P.c * pD P := by
    have := hDn.1
    rw [hxD] at this
    unfold demand at this
    simpa using this
  have hπD : profitDCR P xD xD = profitAtPrice P (pD P) := by
    rw [hxD]
    unfold profitDCR dcrWage
    exact profit_sym_eq P hm.ne' _ _ hDid hDpos
  have hx₂F : eF.x₂ = α := hFs.1.symm
  have hP₂F : eF.P₂ eF.x₁ eF.x₂ = priceFCR P α := by rw [← hFs.2, hpF]
  have hcm : 0 < P.c + P.m * (1 - α) := by
    have : 0 < P.m * (1 - α) := mul_pos hm (by linarith [hαI.2])
    linarith
  have hFid : P.a - P.c * priceFCR P α = -P.k + P.m * ((1 - α) * priceFCR P α) := by
    unfold priceFCR
    field_simp
    ring
  have hFpos : 0 < P.a - P.c * priceFCR P α := by
    have := hFn.1
    rw [hpF, hP₂F] at this
    unfold demand at this
    simpa using this
  have hπF : eF.onPathProfit P fcrWage = profitAtPrice P (priceFCR P α) := by
    unfold TwoStage.onPathProfit TwoStage.profit₁ fcrWage
    have e1 : eF.P₁ eF.x₁ eF.x₂ = priceFCR P α := hpF
    rw [e1, hP₂F, hx₂F]
    exact profit_sym_eq P hm.ne' _ _ hFid hFpos
  have hx₂W : eW.x₂ = wW P := by rw [← hWs.1, hxW]
  have hP₂W : eW.P₂ eW.x₁ eW.x₂ = pW P := by rw [← hWs.2, hpW]
  have hWid : P.a - P.c * pW P = -P.k + P.m * wW P := by
    unfold pW
    field_simp
    ring
  have hWpos : 0 < P.a - P.c * pW P := by
    have := hWn.1
    rw [hpW, hP₂W] at this
    unfold demand at this
    simpa using this
  have hπW : eW.onPathProfit P fwWage = profitAtPrice P (pW P) := by
    unfold TwoStage.onPathProfit TwoStage.profit₁ fwWage
    have e1 : eW.P₁ eW.x₁ eW.x₂ = pW P := hpW
    rw [e1, hP₂W, hxW, hx₂W]
    exact profit_sym_eq P hm.ne' _ _ hWid hWpos
  -- price ranking implies profit ranking
  have rank : ∀ p q : ℝ, p < q → q < pHat P → profitAtPrice P p < profitAtPrice P q :=
    fun p q hpq hq => hmono (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 hq.le) hpq
  have hpFpos : 0 < priceFCR P α := by unfold priceFCR; exact div_pos (by linarith) hcm
  -- strict monotonicity of the FCR price formula in the commission rate
  have hpriceMono : ∀ β γ : ℝ, 0 < P.c + P.m * (1 - γ) → β < γ →
      priceFCR P β < priceFCR P γ := by
    intro β γ hγ hβγ
    unfold priceFCR
    apply div_lt_div_of_pos_left (by linarith) hγ
    nlinarith
  rw [hπD, hπF, hπW]
  have hxD2 : xD.2 = alphaD P := by rw [hxD]
  rw [hxD2]
  refine ⟨?_, ?_, ?_⟩
  · intro hcase
    have hclbm : P.c * P.l < P.b * P.m := by
      rw [div_lt_div_iff₀ hm hc] at hcase; linarith
    have hne : P.c * P.l ≠ P.b * P.m := hclbm.ne
    obtain ⟨h13a, -, h13c⟩ := fcr_vs_dcr P hP' hne α hαI hf0
    have hQ : 0 < cond13 P (alphaD P) := by
      unfold cond13
      have h1 : 0 < (P.b + P.c + P.l + P.m) / ((P.b + P.c) * (P.l + P.m) * alphaD P) :=
        div_pos (by linarith) (mul_pos (mul_pos (by linarith) (by linarith)) hαD0)
      have h2 : (P.b + (1 - alphaD P) * P.l) / ((1 - alphaD P) * (P.c * P.l - P.b * P.m)) < 0 :=
        div_neg_of_pos_of_neg (by have := mul_pos (sub_pos.2 hαD1) hl; linarith) (mul_neg_of_pos_of_neg (by linarith) (by linarith))
      linarith
    have hDF : pD P < priceFCR P α := h13c.2 (h13a.2 hQ)
    obtain ⟨-, hW2, -⟩ := fcr_vs_fw P hP' α hαI hf0
    have hααW : α < alphaW P := hW2.2 hclbm
    -- pW = priceFCR (alphaW), with pW > 0
    have hpWpos : 0 < pW P := by
      have := (price_dcr_vs_fw P hP').2.2.2 hclbm
      have hDpPos : 0 < P.c * (P.b + P.c) * (P.l + 2 * P.m) + P.m * (P.b + 2 * P.c) * (P.l + P.m) := by
        have h1 : 0 < P.c * (P.b + P.c) * (P.l + 2 * P.m) :=
          mul_pos (mul_pos hc (by linarith)) (by linarith)
        have h2 : 0 < P.m * (P.b + 2 * P.c) * (P.l + P.m) :=
          mul_pos (mul_pos hm (by linarith)) (by linarith)
        linarith
      have hpD : 0 < pD P := div_pos hNa hDpPos
      linarith
    have hWeq : pW P * (P.c + P.m * (1 - alphaW P)) = P.a + P.k := by
      unfold alphaW
      have hne0 : pW P ≠ 0 := hpWpos.ne'
      field_simp
      linarith [hWid]
    have hcmW : 0 < P.c + P.m * (1 - alphaW P) := by
      by_contra hcon
      push_neg at hcon
      have : pW P * (P.c + P.m * (1 - alphaW P)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpWpos.le hcon
      linarith
    have hpWF : pW P = priceFCR P (alphaW P) := by
      unfold priceFCR
      field_simp
      linarith [hWeq]
    have hFW : priceFCR P α < pW P := by
      rw [hpWF]; exact hpriceMono α (alphaW P) hcmW hααW
    exact ⟨rank _ _ hDF hFh, rank _ _ hFW hpWh⟩
  · intro hcase hQ
    have hblcl : P.b * P.m < P.c * P.l := by
      rw [div_lt_div_iff₀ hc hm] at hcase; linarith
    have hne : P.c * P.l ≠ P.b * P.m := hblcl.ne'
    obtain ⟨h13a, -, h13c⟩ := fcr_vs_dcr P hP' hne α hαI hf0
    have hDF : pD P < priceFCR P α := h13c.2 (h13a.2 hQ)
    have hWD : pW P < pD P := by
      have h := (price_dcr_vs_fw P hP').2.1
      by_contra hcon
      push_neg at hcon
      have := h.1 hcon
      linarith
    exact ⟨rank _ _ hWD hpDh, rank _ _ hDF hFh⟩
  · intro hcase hQ
    have hblcl : P.b * P.m < P.c * P.l := by
      rw [div_lt_div_iff₀ hc hm] at hcase; linarith
    have hne : P.c * P.l ≠ P.b * P.m := hblcl.ne'
    obtain ⟨-, h13b, -⟩ := fcr_vs_dcr P hP' hne α hαI hf0
    have hααD : α < alphaD P := h13b.2 hQ
    obtain ⟨hW1, -, hW3⟩ := fcr_vs_fw P hP' α hαI hf0
    have hWF : pW P < priceFCR P α := hW3.2 (hW1.2 hblcl)
    have hcmD : 0 < P.c + P.m * (1 - alphaD P) := by
      have : 0 < P.m * (1 - alphaD P) := mul_pos hm (by linarith)
      linarith
    have hpDF : pD P = priceFCR P (alphaD P) := by
      unfold priceFCR
      rw [eq_div_iff hcmD.ne']
      linarith [hDid]
    have hFD : priceFCR P α < pD P := by
      rw [hpDF]; exact hpriceMono α (alphaD P) hcmD hααD
    exact ⟨rank _ _ hWF hFh, rank _ _ hFD hpDh⟩
