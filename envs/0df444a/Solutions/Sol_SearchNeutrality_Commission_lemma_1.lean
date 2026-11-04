-- Prove2me | solution 1 for SearchNeutrality.Commission.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:56:08.636+00:00
-- url     : https://prove2.me/submissions/2e383ee3-91d8-4777-85a5-ebc9a7d6cd94

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model

open SearchNeutrality.Commission

lemma sumC1 (g : CType → ℝ) : ∑ k : CType, g k = g .f + g .t := by
  rw [show (Finset.univ : Finset CType) = {.f, .t} from rfl]
  rw [Finset.sum_pair (by decide)]

/-- own-product demand (times 2) under the neutral ranking -/
noncomputable def dN (ρH ρL p q : ℝ) : ℝ := promDemand ρH ρL p q + nonpromDemand ρH ρL q p

lemma demand_neutral_F (ρH ρL pF pT : ℝ) :
    demand ρH ρL (1/2) neutral pF pT .F = (1/2) * dN ρH ρL pF pT := by
  simp [demand, sumC1, typeDemand, neutral, matchProb, price, Product.other, mass, dN]
  ring

lemma demand_neutral_T (ρH ρL pF pT : ℝ) :
    demand ρH ρL (1/2) neutral pF pT .T = (1/2) * dN ρH ρL pT pF := by
  simp [demand, sumC1, typeDemand, neutral, matchProb, price, Product.other, mass, dN]
  ring

lemma dN_lt (ρH ρL p q : ℝ) (h : p < q) : dN ρH ρL p q = ρH + ρL^2 * (1 - ρH + ρH * q - p) := by
  simp [dN, promDemand, nonpromDemand, h, not_lt.2 h.le]

lemma dN_gt (ρH ρL p q : ℝ) (h : q < p) :
    dN ρH ρL p q = ρH * (1 - ρL^2 * p + ρL^2 * q) + (1 - ρH) * ρL^2 * (1 - p) := by
  simp [dN, promDemand, nonpromDemand, h, not_lt.2 h.le]

lemma dN_eq (ρH ρL p : ℝ) : dN ρH ρL p p = ρH + (1 - ρH) * ρL^2 * (1 - p) := by
  simp [dN, promDemand, nonpromDemand]

lemma dN_le_q (ρH ρL p q : ℝ) (h : p ≤ q) : dN ρH ρL p q = ρH + ρL^2 * (1 - ρH + ρH * q - p) := by
  rcases h.lt_or_eq with h | h
  · exact dN_lt _ _ _ _ h
  · subst h; rw [dN_eq]; ring

lemma dN_ge_q (ρH ρL p q : ℝ) (h : q ≤ p) :
    dN ρH ρL p q = ρH * (1 - ρL^2 * p + ρL^2 * q) + (1 - ρH) * ρL^2 * (1 - p) := by
  rcases h.lt_or_eq with h | h
  · exact dN_gt _ _ _ _ h
  · subst h; rw [dN_eq]; ring

lemma seller_neutral (ρH ρL r pF pT : ℝ) :
    sellerProfit ρH ρL r (1/2) neutral pF pT = (1 - r) * pT * ((1/2) * dN ρH ρL pT pF) := by
  rw [sellerProfit, demand_neutral_T]

lemma platform_neutral (ρH ρL r pF pT : ℝ) :
    platformProfit ρH ρL r (1/2) neutral pF pT
      = pF * ((1/2) * dN ρH ρL pF pT) + r * pT * ((1/2) * dN ρH ρL pT pF) := by
  rw [platformProfit, demand_neutral_F, demand_neutral_T]

theorem solution (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsSEquilibrium ρH ρL r (1 / 2) 1 1 ∧
    (∀ pF pT : ℝ, IsSEquilibrium ρH ρL r (1 / 2) pF pT → pF = 1 ∧ pT = 1) ∧
    platformProfit ρH ρL r (1 / 2) neutral 1 1 = ρH * (1 + r) / 2 ∧
    sellerProfit ρH ρL r (1 / 2) neutral 1 1 = ρH * (1 - r) / 2 := by
  have hH0 : 0 < ρH := by linarith
  have hl2 : ρL ^ 2 < ρH := by nlinarith
  have hl2' : 0 < ρL ^ 2 := by positivity
  have h1r : 0 < 1 - r := by linarith
  refine ⟨⟨⟨by norm_num, le_refl _⟩, ⟨by norm_num, le_refl _⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro q ⟨hq0, hq1⟩
    rw [platform_neutral, platform_neutral, dN_le_q _ _ _ _ hq1, dN_ge_q _ _ _ _ hq1, dN_eq]
    nlinarith [mul_nonneg (sub_nonneg.2 hq1) (by nlinarith : (0:ℝ) ≤ ρH - ρL^2 * q),
      mul_nonneg (mul_nonneg hr0 (mul_nonneg hH0.le hl2'.le)) (sub_nonneg.2 hq1)]
  · intro q ⟨hq0, hq1⟩
    rw [seller_neutral, seller_neutral, dN_le_q _ _ _ _ hq1, dN_eq]
    have : 0 ≤ (1 - q) * (ρH - ρL^2 * q) := mul_nonneg (by linarith) (by nlinarith)
    have := mul_nonneg h1r.le this
    nlinarith
  · intro pF pT ⟨⟨hp0, hp1⟩, ⟨hq0, hq1⟩, hF, hT⟩
    rw [platform_neutral] at hF
    rw [seller_neutral] at hT
    -- step 1: pT ≥ pF
    have hge : pF ≤ pT := by
      by_contra hlt
      push_neg at hlt
      have := hT pF ⟨hp0, hp1⟩
      rw [seller_neutral, dN_le_q _ _ _ _ hlt.le, dN_eq] at this
      have hk : pT * (ρH + ρL^2 * (1 - ρH + ρH * pF - pT)) < pF * (ρH + (1 - ρH) * ρL ^ 2 * (1 - pF)) := by
        have : 0 < (pF - pT) * (ρH + ρL^2 * (1 - ρH - (2 - ρH) * pF + (pF - pT))) := by
          apply mul_pos (by linarith)
          nlinarith [mul_nonneg hl2'.le (sub_nonneg.2 hp1), mul_nonneg (mul_nonneg hl2'.le hH0.le) (sub_nonneg.2 hp1),
            mul_nonneg hl2'.le (sub_nonneg.2 hlt.le)]
        nlinarith
      nlinarith [mul_lt_mul_of_pos_left hk (by linarith : (0:ℝ) < (1 - r) * (1/2))]
    have hle : pT ≤ pF := by
      by_contra hlt
      push_neg at hlt
      have := hF pT ⟨hq0, hq1⟩
      rw [platform_neutral, dN_le_q _ _ _ _ hlt.le, dN_ge_q _ _ _ _ hlt.le, dN_eq] at this
      have hk : pF * (ρH + ρL^2 * (1 - ρH + ρH * pT - pF)) < pT * (ρH + (1 - ρH) * ρL ^ 2 * (1 - pT)) := by
        have : 0 < (pT - pF) * (ρH + ρL^2 * (1 - ρH - (2 - ρH) * pT + (pT - pF))) := by
          apply mul_pos (by linarith)
          nlinarith [mul_nonneg hl2'.le (sub_nonneg.2 hq1), mul_nonneg (mul_nonneg hl2'.le hH0.le) (sub_nonneg.2 hq1),
            mul_nonneg hl2'.le (sub_nonneg.2 hlt.le)]
        nlinarith
      have hk2 : ρH * (1 - ρL^2 * pT + ρL^2 * pF) + (1 - ρH) * ρL^2 * (1 - pT)
          ≤ ρH + (1 - ρH) * ρL ^ 2 * (1 - pT) := by nlinarith [mul_pos hH0 hl2']
      have := mul_le_mul_of_nonneg_left hk2 (mul_nonneg (mul_nonneg hr0 hq0) (by norm_num : (0:ℝ) ≤ 1/2))
      nlinarith
    have heq : pF = pT := le_antisymm hge hle
    subst heq
    have hp : pF = 1 := by
      by_contra hne
      have hlt : pF < 1 := lt_of_le_of_ne hp1 hne
      have := hT 1 ⟨by norm_num, le_refl _⟩
      rw [seller_neutral, dN_ge_q _ _ _ _ hp1, dN_eq] at this
      have hk : pF * (ρH + (1 - ρH) * ρL ^ 2 * (1 - pF)) < 1 * (ρH * (1 - ρL^2 * 1 + ρL^2 * pF) + (1 - ρH) * ρL^2 * (1 - 1)) := by
        have : 0 < (1 - pF) * (ρH - ρH * ρL^2 - pF * (1 - ρH) * ρL^2) := by
          apply mul_pos (by linarith)
          nlinarith [mul_nonneg (mul_nonneg hp0 (by linarith : (0:ℝ) ≤ 1 - ρH)) hl2'.le,
            mul_nonneg (sub_nonneg.2 hp1) (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ρH) hl2'.le)]
        nlinarith
      nlinarith [mul_lt_mul_of_pos_left hk (by linarith : (0:ℝ) < (1 - r) * (1/2))]
    exact ⟨hp, hp⟩
  · rw [platform_neutral, dN_eq]; ring
  · rw [seller_neutral, dN_eq]; ring
