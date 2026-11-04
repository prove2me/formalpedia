-- Prove2me | solution 1 for SearchNeutrality.Commission.proposition_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:52:40.433062+00:00
-- url     : https://prove2.me/submissions/d85533a8-989c-4dd7-b90f-613c381481e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model
import Definitions.Def_SearchNeutrality_Commission_ClosedForms
import Theorems.Thm_SearchNeutrality_Commission_lemma_1
import Theorems.Thm_SearchNeutrality_Commission_proposition_4_1
import Theorems.Thm_SearchNeutrality_Commission_proposition_4_2
import Theorems.Thm_SearchNeutrality_Commission_ns_fixed_equilibrium_half
import Theorems.Thm_SearchNeutrality_Commission_cs_ns_display_half

open SearchNeutrality.Commission

lemma sumC (g : CType → ℝ) : ∑ k : CType, g k = g .f + g .t := by
  rw [show (Finset.univ : Finset CType) = {.f, .t} from rfl]
  rw [Finset.sum_pair (by decide)]

lemma demand_fAll_F (ρH ρL pF pT : ℝ) (h : pT < pF) :
    demand ρH ρL (1/2) fPrimeAll pF pT .F
      = (1/2) * (ρH * (1 - ρL^2 * pF + ρL^2 * pT)) + (1/2) * (ρL * (1 - ρH^2 * pF + ρH^2 * pT)) := by
  simp [demand, sumC, typeDemand, fPrimeAll, promDemand, matchProb, price, Product.other, mass, h]
  norm_num

lemma demand_fAll_T (ρH ρL pF pT : ℝ) (h : pT < pF) :
    demand ρH ρL (1/2) fPrimeAll pF pT .T
      = (1/2) * (ρL^2 * (1 - ρH + ρH * pF - pT)) + (1/2) * (ρH^2 * (1 - ρL + ρL * pF - pT)) := by
  simp [demand, sumC, typeDemand, fPrimeAll, nonpromDemand, matchProb, price, Product.other, mass, h]
  norm_num

lemma cs_neutral_one (ρH ρL : ℝ) : consumerSurplus ρH ρL (1/2) neutral 1 1 = 0 := by
  have key : ∀ k : CType, ∫ c in (0:ℝ)..1,
      typeSurplus (matchProb ρH ρL k (neutral k)) (matchProb ρH ρL k (neutral k).other)
        (price 1 1 (neutral k)) (price 1 1 (neutral k).other) c = 0 := by
    intro k
    have : ∀ ρ1 ρ2 : ℝ, ∀ p q : ℝ, p = 1 → q = 1 →
        ∫ c in (0:ℝ)..1, typeSurplus ρ1 ρ2 p q c = 0 := by
      intro ρ1 ρ2 p q hp hq
      subst hp; subst hq
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
      · simp
      · intro c hc
        rw [Set.uIcc_of_le (by norm_num)] at hc
        simp only [typeSurplus, sub_self, mul_zero, zero_sub]
        rw [max_eq_right (by linarith [hc.1])]
        ring
    apply this <;> cases k <;> rfl
  simp [consumerSurplus, sumC, key]

lemma np_le_p (a b pF q : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hp0 : 0 ≤ pF) (hp1 : pF ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    nonpromDemand b a pF q ≤ promDemand a b q pF := by
  unfold nonpromDemand promDemand
  have haa : a ^ 2 ≤ a := by nlinarith
  split_ifs with h1 h2 h2
  · linarith
  · nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ b * (1 - pF) + q by nlinarith)]
  · have : b ^ 2 * (q - pF) ≤ q - pF := by
      have hb2 : b ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 hb2) (show (0:ℝ) ≤ q - pF by linarith)]
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 hq1), mul_nonneg hb0.le (mul_nonneg (sq_nonneg a) (sub_nonneg.2 hq1)),
      mul_nonneg (sub_nonneg.2 haa) (sub_nonneg.2 hq1), mul_nonneg ha0.le (sub_nonneg.2 this), mul_nonneg ha0.le hp0]
  · nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 hq1), mul_nonneg hb0.le (mul_nonneg (sq_nonneg a) (sub_nonneg.2 hq1)),
      mul_nonneg (sq_nonneg a) hq0]

lemma seller_mono (ρH ρL r pF q : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr1 : r < 1) (hpF : pF ∈ Set.Icc (0:ℝ) 1) (hq : q ∈ Set.Icc (0:ℝ) 1) (σ : Ranking) :
    sellerProfit ρH ρL r (1/2) fPrimeAll pF q ≤ sellerProfit ρH ρL r (1/2) σ pF q := by
  obtain ⟨hp0, hp1⟩ := hpF
  obtain ⟨hq0, hq1⟩ := hq
  have hk : ∀ (k : CType) (prom : Product),
      typeDemand ρH ρL pF q k .F .T ≤ typeDemand ρH ρL pF q k prom .T := by
    intro k prom
    cases k <;> cases prom <;> simp [typeDemand, matchProb, price, Product.other]
    · exact np_le_p ρL ρH pF q hL (by linarith) (by linarith) hH hp0 hp1 hq0 hq1
    · exact np_le_p ρH ρL pF q (by linarith) hH hL (by linarith) hp0 hp1 hq0 hq1
  unfold sellerProfit demand
  rw [sumC, sumC]
  have h1 := hk .f (σ .f)
  have h2 := hk .t (σ .t)
  simp only [fPrimeAll, mass]
  have : 0 ≤ (1 - r) * q := mul_nonneg (by linarith) hq0
  nlinarith

lemma platform_decomp (ρH ρL r α : ℝ) (σ : Ranking) (pF pT : ℝ) :
    platformProfit ρH ρL r α σ pF pT
      = mass α .f * platformTypeProfit ρH ρL r pF pT .f (σ .f)
        + mass α .t * platformTypeProfit ρH ρL r pF pT .t (σ .t) := by
  unfold platformProfit demand platformTypeProfit
  rw [sumC, sumC]; ring

lemma ns_to_fixed (ρH ρL r pF pT : ℝ) (σ : ℝ → ℝ → Ranking) (hL : 0 < ρL) (hLH : ρL < ρH)
    (hH : ρH < 1) (hr1 : r < 1)
    (hNS : IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ) (hσ : σ pF pT = fPrimeAll) :
    IsPriceEquilibrium ρH ρL r (1 / 2) fPrimeAll pF pT := by
  obtain ⟨hopt, hpF, hpT, hF, hT⟩ := hNS
  refine ⟨hpF, hpT, ?_, ?_⟩
  · intro q hq
    have := hF q hq
    rw [hσ] at this
    refine le_trans ?_ this
    rw [platform_decomp, platform_decomp]
    have h1 := hopt q hq pT hpT .f (fPrimeAll .f)
    have h2 := hopt q hq pT hpT .t (fPrimeAll .t)
    simp only [mass]
    linarith
  · intro q hq
    have := hT q hq
    rw [hσ] at this
    exact le_trans (seller_mono ρH ρL r pF q hL hLH hH hr1 hpF hq (σ pF q)) this

lemma seller_fAll_lt (ρH ρL r pF pT : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr1 : r < 1) (hpF : pF ∈ Set.Icc (0:ℝ) 1) (hpT : pT ∈ Set.Icc (0:ℝ) 1) (hlt : pT < pF) :
    sellerProfit ρH ρL r (1/2) fPrimeAll pF pT < ρH * (1 - r) / 2 := by
  obtain ⟨hp0, hp1⟩ := hpF
  obtain ⟨hq0, hq1⟩ := hpT
  unfold sellerProfit
  rw [demand_fAll_T _ _ _ _ hlt]
  have hD : (1/2) * (ρL^2 * (1 - ρH + ρH * pF - pT)) + (1/2) * (ρH^2 * (1 - ρL + ρL * pF - pT))
      ≤ (1/2) * (ρL^2 + ρH^2) * (1 - pT) := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ρL) (by linarith : (0:ℝ) ≤ ρH)) (sub_nonneg.2 hp1),
      mul_nonneg (mul_nonneg (sq_nonneg ρH) hL.le) (sub_nonneg.2 hp1)]
  have hq : pT * (1 - pT) ≤ 1/4 := by nlinarith [sq_nonneg (pT - 1/2)]
  have hA : ρL^2 + ρH^2 < 4 * ρH := by nlinarith
  have h1r : 0 < 1 - r := by linarith
  have : pT * ((1/2) * (ρL^2 * (1 - ρH + ρH * pF - pT)) + (1/2) * (ρH^2 * (1 - ρL + ρL * pF - pT)))
      < ρH / 2 := by
    calc _ ≤ pT * ((1/2) * (ρL^2 + ρH^2) * (1 - pT)) := mul_le_mul_of_nonneg_left hD hq0
      _ = (1/2) * (ρL^2 + ρH^2) * (pT * (1 - pT)) := by ring
      _ ≤ (1/2) * (ρL^2 + ρH^2) * (1/4) := by
          apply mul_le_mul_of_nonneg_left hq; positivity
      _ < ρH / 2 := by nlinarith
  calc (1 - r) * pT * _ = (1 - r) * (pT * ((1/2) * (ρL^2 * (1 - ρH + ρH * pF - pT)) + (1/2) * (ρH^2 * (1 - ρL + ρL * pF - pT)))) := by ring
    _ < (1 - r) * (ρH / 2) := mul_lt_mul_of_pos_left this h1r
    _ = ρH * (1 - r) / 2 := by ring

lemma foc_closed (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 - ρH * ρL * (2 * pFNS ρH ρL r (1/2) - pTNS ρH ρL r (1/2))
        + r * (ρH * ρL) * pTNS ρH ρL r (1/2) = 0 ∧
    (ρH^2 + ρL^2) * (1 - pTNS ρH ρL r (1/2)) - ρH * ρL * (ρH + ρL) * (1 - pFNS ρH ρL r (1/2))
        - (ρH^2 + ρL^2) * pTNS ρH ρL r (1/2) = 0 := by
  have hH0 : 0 < ρH := by linarith
  set α : ℝ := 1/2 with hα
  set nF := ((1 - α) ^ 2 * ρL * ρH ^ 2 * (2 + (1 - ρL) * ρH ^ 2 * (1 + r))
      + α ^ 2 * ρH * ρL ^ 2 * (2 + (1 - ρH) * ρL ^ 2 * (1 + r))
      + α * (1 - α) * (ρH ^ 2 * ρL ^ 2 * (ρH + ρL - 2 * ρH * ρL) * (1 + r)
          + 2 * (ρH ^ 3 + ρL ^ 3))) with hnF
  set dF := (ρH * ρL * ((1 - α) * ρH + α * ρL)
        * ((1 - α) * (4 - (1 + r) * ρL) * ρH ^ 2 + α * (4 - (1 + r) * ρH) * ρL ^ 2)) with hdF
  set nT := ((1 - α) * (ρL + 2 * (1 - ρL) * ρH ^ 2) + α * (ρH + 2 * (1 - ρH) * ρL ^ 2)) with hnT
  set dT := ((1 - α) * ρH ^ 2 * (4 - (1 + r) * ρL) + α * ρL ^ 2 * (4 - (1 + r) * ρH)) with hdT
  have e1 : pFNS ρH ρL r α = nF / dF := rfl
  have e2 : pTNS ρH ρL r α = nT / dT := rfl
  have h4L : 0 < 4 - (1 + r) * ρL := by nlinarith
  have h4H : 0 < 4 - (1 + r) * ρH := by nlinarith
  have hdT0 : dT ≠ 0 := by rw [hdT, hα]; positivity
  have hdF0 : dF ≠ 0 := by rw [hdF, hα]; positivity
  have hx : pFNS ρH ρL r α * dF = nF := by rw [e1]; field_simp
  have hy : pTNS ρH ρL r α * dT = nT := by rw [e2]; field_simp
  set x := pFNS ρH ρL r α
  set y := pTNS ρH ρL r α
  have hprod : dF * dT ≠ 0 := mul_ne_zero hdF0 hdT0
  constructor
  · have : (1 - ρH * ρL * (2 * x - y) + r * (ρH * ρL) * y) * (dF * dT) = 0 := by
      linear_combination (-2 * ρH * ρL * dT) * hx + (ρH * ρL * (1 + r) * dF) * hy
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hprod
  · have : ((ρH^2 + ρL^2) * (1 - y) - ρH * ρL * (ρH + ρL) * (1 - x) - (ρH^2 + ρL^2) * y) * (dF * dT) = 0 := by
      linear_combination (ρH * ρL * (ρH + ρL) * dT) * hx + (-2 * (ρH^2 + ρL^2) * dF) * hy
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hprod
lemma final1 (y r : ℝ) (hy : 0 ≤ y) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : y * (29204/10000 - r) ≤ 102/100) :
    2 * (1 + y * (1 + r)) * (1 + y * (1 - r)) + 8 * r * y ^ 2 < 3881196/1000000 * (1 + r) := by
  have hY : y ≤ (102/100) / (29204/10000 - r) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hy2 : y ≤ 102/100 / (19204/10000) := le_trans hY (by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
  nlinarith [mul_nonneg hy hr0, mul_nonneg (mul_nonneg hy hy) hr0, mul_nonneg hy (sub_nonneg.2 hr1.le),
    mul_nonneg (mul_nonneg hy hr0) (sub_nonneg.2 hr1.le), mul_nonneg hr0 (sub_nonneg.2 hr1.le)]

lemma bnd_basic (ρH ρL : ℝ) (hb : 99/100 < ρL) (hLH : ρL < ρH) (hH : ρH < 1) :
    0 < ρH * ρL ∧ ρH * ρL ≤ 1 ∧ 970299/1000000 ≤ ρH * ρL * ρH ∧ ρH + ρL ≤ 2 ∧
    ρH^2 + ρL^2 ≤ 2 ∧ 39204/10000 ≤ 2 * (ρH^2 + ρL^2) ∧ (ρH + ρL) * (ρH * ρL) ≤ 2 ∧
    (ρH^2 + ρL^2) - ρH * ρL * (ρH + ρL) + (ρH + ρL) / 2 ≤ 102/100 := by
  have hL0 : 0 < ρL := by linarith
  have hH0 : 0 < ρH := by linarith
  have hP0 : 0 < ρH * ρL := by positivity
  have hP1 : ρH * ρL ≤ 1 := by nlinarith
  have hP9 : 9801/10000 ≤ ρH * ρL := by nlinarith
  refine ⟨hP0, hP1, by nlinarith, by linarith, by nlinarith, by nlinarith, by nlinarith, ?_⟩
  have : (ρH^2 + ρL^2) - ρH * ρL * (ρH + ρL) = ρH^2 * (1 - ρL) + ρL^2 * (1 - ρH) := by ring
  rw [this]
  have h1 : ρH^2 * (1 - ρL) ≤ 1 - ρL := by
    have : ρH^2 ≤ 1 := by nlinarith
    nlinarith
  have h2 : ρL^2 * (1 - ρH) ≤ 1 - ρH := by
    have : ρL^2 ≤ 1 := by nlinarith
    nlinarith
  linarith

lemma poly_le (s P A y r : ℝ) (hs2 : s ≤ 2) (hs0 : 0 ≤ s) (hP0 : 0 < P) (hP1 : P ≤ 1) (hA2 : A ≤ 2)
    (hA0 : 0 ≤ A) (hy0 : 0 ≤ y) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    s * (1 + P * y * (1 + r)) * (1 + P * y * (1 - r)) + 4 * P * r * A * y ^ 2
      ≤ 2 * (1 + y * (1 + r)) * (1 + y * (1 - r)) + 8 * r * y ^ 2 := by
  have hPy : P * y ≤ y := by nlinarith
  have hPy0 : 0 ≤ P * y := by positivity
  have t2 : 0 ≤ 1 + P * y * (1 - r) := by
    have : 0 ≤ P * y * (1 - r) := mul_nonneg hPy0 (by linarith)
    linarith
  have a1 : (1 + P * y * (1 + r)) ≤ 1 + y * (1 + r) := by
    have := mul_le_mul_of_nonneg_right hPy (by linarith : (0:ℝ) ≤ 1 + r); linarith
  have a2 : (1 + P * y * (1 - r)) ≤ 1 + y * (1 - r) := by
    have := mul_le_mul_of_nonneg_right hPy (by linarith : (0:ℝ) ≤ 1 - r); linarith
  have a3 : (1 + P * y * (1 + r)) * (1 + P * y * (1 - r)) ≤ (1 + y * (1 + r)) * (1 + y * (1 - r)) :=
    mul_le_mul a1 a2 t2 (by nlinarith)
  have a4 : s * ((1 + P * y * (1 + r)) * (1 + P * y * (1 - r))) ≤ 2 * ((1 + y * (1 + r)) * (1 + y * (1 - r))) :=
    mul_le_mul hs2 a3 (by positivity) (by norm_num)
  have a5 : P * A ≤ 2 := by nlinarith
  have a6 : 4 * P * r * A * y ^ 2 ≤ 8 * r * y ^ 2 := by
    have : 0 ≤ r * y ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right a5 this
    nlinarith
  nlinarith

lemma interior_bound (ρH ρL r x y : ℝ) (hb : 99/100 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hy0 : 0 ≤ y) (hlt : y < x)
    (E1 : 1 - ρH * ρL * (2 * x - y) + r * (ρH * ρL) * y = 0)
    (E2 : (ρH^2 + ρL^2) * (1 - y) - ρH * ρL * (ρH + ρL) * (1 - x) - (ρH^2 + ρL^2) * y = 0) :
    platformProfit ρH ρL r (1/2) fPrimeAll x y < ρH * (1 + r) / 2 := by
  unfold platformProfit
  rw [demand_fAll_F _ _ _ _ hlt, demand_fAll_T _ _ _ _ hlt]
  have key : 8 * (ρH * ρL) * (x * ((1/2) * (ρH * (1 - ρL^2 * x + ρL^2 * y)) + (1/2) * (ρL * (1 - ρH^2 * x + ρH^2 * y)))
      + r * y * ((1/2) * (ρL^2 * (1 - ρH + ρH * x - y)) + (1/2) * (ρH^2 * (1 - ρL + ρL * x - y))))
      = (ρH + ρL) * (1 + (ρH * ρL) * y * (1 + r)) * (1 + (ρH * ρL) * y * (1 - r))
        + 4 * (ρH * ρL) * r * (ρH^2 + ρL^2) * y ^ 2 := by
    linear_combination ((ρH + ρL) * ((ρH * ρL) * r * y + 2 * (ρH * ρL) * x - (ρH * ρL) * y - 1)) * E1
      + (4 * (ρH * ρL) * r * y) * E2
  have yeq : y * (2 * (ρH^2 + ρL^2) - (ρH + ρL) * (ρH * ρL) * (1 + r) / 2)
      = (ρH^2 + ρL^2) - ρH * ρL * (ρH + ρL) + (ρH + ρL) / 2 := by
    linear_combination (-((ρH + ρL)/2)) * E1 - E2
  obtain ⟨hP0, hP1, hPlo, hs2, hA2, hA4, hsP, hN⟩ := bnd_basic ρH ρL hb hLH hH
  have hb2 : y * (29204/10000 - r) ≤ 102/100 := by
    have hD : 29204/10000 - r ≤ 2 * (ρH^2 + ρL^2) - (ρH + ρL) * (ρH * ρL) * (1 + r) / 2 := by
      have := mul_le_mul_of_nonneg_right hsP (by linarith : (0:ℝ) ≤ 1 + r)
      linarith
    have := mul_le_mul_of_nonneg_left hD hy0
    linarith
  have hf := final1 y r hy0 hr0 hr1 hb2
  have hle := poly_le (ρH + ρL) (ρH * ρL) (ρH^2 + ρL^2) y r hs2 (by linarith) hP0 hP1 hA2
    (by positivity) hy0 hr0 hr1
  have hR : 3881196/1000000 * (1 + r) ≤ 8 * (ρH * ρL) * (ρH * (1 + r) / 2) := by
    have := mul_le_mul_of_nonneg_right hPlo (by linarith : (0:ℝ) ≤ 1 + r)
    nlinarith
  have h8 : 0 < 8 * (ρH * ρL) := by positivity
  refine lt_of_mul_lt_mul_left ?_ h8.le
  rw [key]
  linarith

lemma corner_bound (ρH ρL r : ℝ) (hb : 99/100 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr1 : r < 1) (hr : 3 - 2 / (ρH * ρL) ≤ r) :
    platformProfit ρH ρL r (1/2) fPrimeAll 1 (1/2) < ρH * (1 + r) / 2 := by
  unfold platformProfit
  rw [demand_fAll_F _ _ _ _ (by norm_num), demand_fAll_T _ _ _ _ (by norm_num)]
  have hP : 9801/10000 ≤ ρH * ρL := by nlinarith
  have hP0 : 0 < ρH * ρL := by linarith
  have hr' : 3 * (ρH * ρL) - 2 ≤ r * (ρH * ρL) := by
    have := mul_le_mul_of_nonneg_right hr hP0.le
    rw [sub_mul, div_mul_cancel₀ _ hP0.ne'] at this
    linarith
  have hr9 : 95/100 ≤ r := by nlinarith
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - ρH) (by linarith : (0:ℝ) < 1 - ρL)]

lemma csNS_pos (ρH ρL pF pT : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hp1 : pF ≤ 1) (hlt : pT < pF) : 0 < csNS ρH ρL (1/2) pF pT := by
  unfold csNS
  have hH0 : 0 < ρH := by linarith
  have h1 : 0 ≤ ((1/2:ℝ) * ρH + (1 - 1/2) * ρL) * (1 - pF) := mul_nonneg (by positivity) (by linarith)
  have h2 : 0 < (1/2:ℝ) * ρL ^ 2 / 2 * (ρH * (pF - pT) ^ 2 + (1 - ρH) * (1 - pT) ^ 2) := by
    have : 0 < ρH * (pF - pT) ^ 2 := mul_pos hH0 (by nlinarith)
    have : 0 ≤ (1 - ρH) * (1 - pT) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    positivity
  have h3 : 0 ≤ (1 - 1/2:ℝ) * ρH ^ 2 / 2 * (ρL * (pF - pT) ^ 2 + (1 - ρL) * (1 - pT) ^ 2) := by
    have : 0 ≤ (1 - ρL) * (1 - pT) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    positivity
  linarith


theorem solution :
    (∀ ρH ρL r : ℝ, 0 < ρL → ρL < ρH → ρH < 1 → 0 ≤ r → r < 1 →
      (ρL / ρH < r →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        ∀ qF qT : ℝ, IsSEquilibrium ρH ρL r (1 / 2) qF qT →
          pF = qF ∧ pT = qT ∧ σ pF pT = neutral ∧
          platformProfit ρH ρL r (1 / 2) (σ pF pT) pF pT
            = platformProfit ρH ρL r (1 / 2) neutral qF qT ∧
          sellerProfit ρH ρL r (1 / 2) (σ pF pT) pF pT
            = sellerProfit ρH ρL r (1 / 2) neutral qF qT ∧
          consumerSurplus ρH ρL (1 / 2) (σ pF pT) pF pT
            = consumerSurplus ρH ρL (1 / 2) neutral qF qT) ∧
      (r < ρL / ρH →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        ∀ qF qT : ℝ, IsSEquilibrium ρH ρL r (1 / 2) qF qT →
          consumerSurplus ρH ρL (1 / 2) neutral qF qT
            < consumerSurplus ρH ρL (1 / 2) (σ pF pT) pF pT ∧
          sellerProfit ρH ρL r (1 / 2) (σ pF pT) pF pT
            < sellerProfit ρH ρL r (1 / 2) neutral qF qT)) ∧
    (∃ ρbar : ℝ, ρbar < 1 ∧
      ∀ ρH ρL r : ℝ, 0 < ρL → ρbar < ρL → ρL < ρH → ρH < 1 → 0 ≤ r → r < ρL / ρH →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        ∀ qF qT : ℝ, IsSEquilibrium ρH ρL r (1 / 2) qF qT →
          platformProfit ρH ρL r (1 / 2) (σ pF pT) pF pT
            < platformProfit ρH ρL r (1 / 2) neutral qF qT) := by
  refine ⟨fun ρH ρL r hL hLH hH hr0 hr1 => ⟨?_, ?_⟩, ?_⟩
  · intro hr pF pT σ hNS qF qT hS
    obtain ⟨hσ, hpF, hpT⟩ := ((proposition_4_1 ρH ρL r hL hLH hH hr0 hr1).1 hr).2 pF pT σ hNS
    obtain ⟨hqF, hqT⟩ := (lemma_1 ρH ρL r hL hLH hH hr0 hr1).2.1 qF qT hS
    subst hpF hpT hqF hqT
    exact ⟨rfl, rfl, hσ, by rw [hσ], by rw [hσ], by rw [hσ]⟩
  · intro hr pF pT σ hNS qF qT hS
    obtain ⟨hσ, hlt⟩ := ((proposition_4_2.1 ρH ρL r hL hLH hH hr0 hr).2.1) pF pT σ hNS
    have hl1 := lemma_1 ρH ρL r hL hLH hH hr0 hr1
    obtain ⟨hqF, hqT⟩ := hl1.2.1 qF qT hS
    subst hqF hqT
    obtain ⟨_, hpF, hpT, _, _⟩ := hNS
    rw [hσ]
    refine ⟨?_, ?_⟩
    · rw [cs_neutral_one, cs_ns_display_half ρH ρL hL hLH hH pF pT hpF hpT hlt.le]
      exact csNS_pos ρH ρL pF pT hL hLH hH hpF.2 hlt
    · rw [hl1.2.2.2]
      exact seller_fAll_lt ρH ρL r pF pT hL hLH hH hr1 hpF hpT hlt
  · refine ⟨99/100, by norm_num, ?_⟩
    intro ρH ρL r hL hb hLH hH hr0 hr pF pT σ hNS qF qT hS
    have hr1 : r < 1 := lt_trans hr ((div_lt_one (by linarith)).2 hLH)
    obtain ⟨hσ, hlt⟩ := ((proposition_4_2.1 ρH ρL r hL hLH hH hr0 hr).2.1) pF pT σ hNS
    have hl1 := lemma_1 ρH ρL r hL hLH hH hr0 hr1
    obtain ⟨hqF, hqT⟩ := hl1.2.1 qF qT hS
    subst hqF hqT
    rw [hl1.2.2.1, hσ]
    have hPE := ns_to_fixed ρH ρL r pF pT σ hL hLH hH hr1 hNS hσ
    have hpT := hNS.2.2.1
    rcases (ns_fixed_equilibrium_half ρH ρL r hL hLH hH hr0 hr1 pF pT).1 hPE with
      ⟨_, hx, hy⟩ | ⟨hc, hx, hy⟩
    · obtain ⟨E1, E2⟩ := foc_closed ρH ρL r hL hLH hH hr0 hr1
      rw [← hx, ← hy] at E1 E2
      exact interior_bound ρH ρL r pF pT hb hLH hH hr0 hr1 hpT.1 hlt E1 E2
    · subst hx hy
      exact corner_bound ρH ρL r hb hLH hH hr1 hc
