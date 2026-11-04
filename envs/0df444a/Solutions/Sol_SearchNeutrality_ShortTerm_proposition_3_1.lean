-- Prove2me | solution 1 for SearchNeutrality.ShortTerm.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:46:38.139414+00:00
-- url     : https://prove2.me/submissions/a8507e21-1cb9-4c75-bde7-e5e796337abc

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model

namespace Aux_SN31
open SearchNeutrality.ShortTerm

lemma sT_low (ρH ρL r α pF q : ℝ) (h : q ≤ pF) :
    sellerProfit ρH ρL r α neutral pF q =
      (1-r)*q*((1-α)*ρH + α*(ρL^2*(1-ρH+ρH*pF-q))) := by
  unfold sellerProfit demand typeDemand
  rw [show (Finset.univ : Finset CType) = {CType.f, CType.t} from rfl, Finset.sum_pair (by decide)]
  simp only [neutral, Product.other, matchProb, price, mass, promDemand, nonpromDemand,
    reduceCtorEq, ↓reduceIte]
  rcases lt_or_eq_of_le h with h' | h'
  · simp only [gt_iff_lt, h', not_lt.2 h'.le, if_true, if_false]; ring
  · subst h'; simp only [gt_iff_lt, lt_irrefl, if_false]; ring

lemma sT_high (ρH ρL r α pF q : ℝ) (h : pF ≤ q) :
    sellerProfit ρH ρL r α neutral pF q =
      (1-r)*q*((1-α)*ρH*(1-ρL^2*(q-pF)) + α*(1-ρH)*ρL^2*(1-q)) := by
  unfold sellerProfit demand typeDemand
  rw [show (Finset.univ : Finset CType) = {CType.f, CType.t} from rfl, Finset.sum_pair (by decide)]
  simp only [neutral, Product.other, matchProb, price, mass, promDemand, nonpromDemand,
    reduceCtorEq, ↓reduceIte]
  rcases lt_or_eq_of_le h with h' | h'
  · simp only [gt_iff_lt, h', not_lt.2 h'.le, if_true, if_false]; ring
  · subst h'; simp only [gt_iff_lt, lt_irrefl, if_false]; ring

lemma sF_low (ρH ρL r α pT q : ℝ) (h : q ≤ pT) :
    platformProfit ρH ρL r α neutral q pT =
      q*(α*ρH + (1-α)*ρL^2*(1-ρH+ρH*pT-q)) +
        r*pT*(α*(1-ρH)*ρL^2*(1-pT) + (1-α)*ρH*(1-ρL^2*pT+ρL^2*q)) := by
  unfold platformProfit demand typeDemand
  rw [show (Finset.univ : Finset CType) = {CType.f, CType.t} from rfl, Finset.sum_pair (by decide),
    Finset.sum_pair (by decide)]
  simp only [neutral, Product.other, matchProb, price, mass, promDemand, nonpromDemand,
    reduceCtorEq, ↓reduceIte]
  rcases lt_or_eq_of_le h with h' | h'
  · simp only [gt_iff_lt, h', not_lt.2 h'.le, if_true, if_false]; ring
  · subst h'; simp only [gt_iff_lt, lt_irrefl, if_false]; ring

lemma sF_high (ρH ρL r α pT q : ℝ) (h : pT ≤ q) :
    platformProfit ρH ρL r α neutral q pT =
      q*(α*ρH*(1-ρL^2*(q-pT)) + (1-α)*(1-ρH)*ρL^2*(1-q)) +
        r*pT*(α*ρL^2*(1-ρH+ρH*q-pT) + (1-α)*ρH) := by
  unfold platformProfit demand typeDemand
  rw [show (Finset.univ : Finset CType) = {CType.f, CType.t} from rfl, Finset.sum_pair (by decide),
    Finset.sum_pair (by decide)]
  simp only [neutral, Product.other, matchProb, price, mass, promDemand, nonpromDemand,
    reduceCtorEq, ↓reduceIte]
  rcases lt_or_eq_of_le h with h' | h'
  · simp only [gt_iff_lt, h', not_lt.2 h'.le, if_true, if_false]; ring
  · subst h'; simp only [gt_iff_lt, lt_irrefl, if_false]; ring


lemma prom_le (ρ1 ρ2 p1 p2 : ℝ) (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2) :
    promDemand ρ1 ρ2 p1 p2 ≤ ρ1 := by
  unfold promDemand
  split_ifs with h
  · nlinarith [mul_nonneg (mul_nonneg h2 h2) (sub_nonneg.2 h.le)]
  · exact le_rfl

lemma prom_ge (ρ1 ρ2 p1 p2 η : ℝ) (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2) (h2' : ρ2 ≤ 1)
    (hη : 0 ≤ η) (hp : p1 - p2 ≤ η) :
    ρ1 * (1 - η) ≤ promDemand ρ1 ρ2 p1 p2 := by
  unfold promDemand
  split_ifs with h
  · have : ρ2 ^ 2 * (p1 - p2) ≤ η := by
      have : ρ2 ^ 2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith
  · nlinarith

lemma nonprom_nonneg (ρ1 ρ2 p1 p2 : ℝ) (h1 : 0 ≤ ρ1) (h1' : ρ1 ≤ 1) (hp1 : p1 ≤ 1)
    (hp2 : p2 ≤ 1) : 0 ≤ nonpromDemand ρ1 ρ2 p1 p2 := by
  unfold nonpromDemand
  split_ifs with h
  · apply mul_nonneg (sq_nonneg _); nlinarith
  · apply mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)); linarith

lemma nonprom_le (ρ1 ρ2 p1 p2 : ℝ) (h1 : 0 ≤ ρ1) (h1' : ρ1 ≤ 1) (h2 : 0 ≤ ρ2) (h2' : ρ2 ≤ 1)
    (hp1 : p1 ≤ 1) (hp2 : p2 ≤ 1) : nonpromDemand ρ1 ρ2 p1 p2 ≤ 1 - p2 := by
  unfold nonpromDemand
  have hs : ρ2 ^ 2 ≤ 1 := by nlinarith
  split_ifs with h
  · have hx : 0 ≤ 1 - ρ1 + ρ1 * p1 - p2 := by nlinarith
    have : 1 - ρ1 + ρ1 * p1 - p2 ≤ 1 - p2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs hx]
  · have : (1 - ρ1) * ρ2 ^ 2 ≤ 1 := by nlinarith
    nlinarith

lemma nonprom_half (ρ1 ρ2 p1 : ℝ) (h1 : 0 ≤ ρ1) (h1' : ρ1 ≤ 1) (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1) :
    (1 - ρ1) * ρ2 ^ 2 / 2 ≤ nonpromDemand ρ1 ρ2 p1 (1/2) := by
  unfold nonpromDemand
  split_ifs with h
  · nlinarith [sq_nonneg ρ2, mul_nonneg (sq_nonneg ρ2) (mul_nonneg h1 hp1)]
  · nlinarith

lemma prom_half (ρ1 ρ2 p2 : ℝ) (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2) (h2' : ρ2 ≤ 1) (hp2 : 0 ≤ p2) :
    ρ1 / 2 ≤ promDemand ρ1 ρ2 (1/2) p2 := by
  have := prom_ge ρ1 ρ2 (1/2) p2 (1/2) h1 h2 h2' (by norm_num) (by linarith)
  linarith

lemma mp_bounds (ρH ρL : ℝ) (h : ρL ≤ ρH) (k : CType) (j : Product) :
    ρL ≤ matchProb ρH ρL k j ∧ matchProb ρH ρL k j ≤ ρH := by
  cases k <;> cases j <;> simp [matchProb, h]

lemma ptp_F (ρH ρL r pF pT : ℝ) (k : CType) : platformTypeProfit ρH ρL r pF pT k .F =
    pF * promDemand (matchProb ρH ρL k .F) (matchProb ρH ρL k .T) pF pT +
      r * pT * nonpromDemand (matchProb ρH ρL k .F) (matchProb ρH ρL k .T) pF pT := by
  simp [platformTypeProfit, typeDemand, Product.other, price]

lemma ptp_T (ρH ρL r pF pT : ℝ) (k : CType) : platformTypeProfit ρH ρL r pF pT k .T =
    pF * nonpromDemand (matchProb ρH ρL k .T) (matchProb ρH ρL k .F) pT pF +
      r * pT * promDemand (matchProb ρH ρL k .T) (matchProb ρH ρL k .F) pT pF := by
  simp [platformTypeProfit, typeDemand, Product.other, price]

/-- Near `(1,1)` the platform strictly prefers to make `F` prominent for every type. -/
lemma rank_F (ρH ρL r pF pT η : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hC : r * ρH ≤ 64 / 100 * ρL) (hη0 : 0 < η) (hη1 : η ≤ ρL / 10)
    (hF : 1 - η < pF) (hF1 : pF ≤ 1) (hT : 1 - η < pT) (hT1 : pT ≤ 1) (k : CType) :
    platformTypeProfit ρH ρL r pF pT k .T < platformTypeProfit ρH ρL r pF pT k .F := by
  rw [ptp_F, ptp_T]
  obtain ⟨a1, a2⟩ := mp_bounds ρH ρL hLH.le k .F
  obtain ⟨b1, b2⟩ := mp_bounds ρH ρL hLH.le k .T
  set x := matchProb ρH ρL k .F
  set y := matchProb ρH ρL k .T
  have key : r * y ≤ 64 / 100 * x := by
    have : r * y ≤ 64 / 100 * ρL := by nlinarith
    cases k
    · simp only [x, matchProb] at *; nlinarith
    · simp only [x, matchProb] at *; linarith
  have e1 := prom_ge x y pF pT η (by linarith) (by linarith) (by linarith) hη0.le (by linarith)
  have e2 := nonprom_nonneg x y pF pT (by linarith) (by linarith) hF1 hT1
  have e3 := nonprom_le y x pT pF (by linarith) (by linarith) (by linarith) (by linarith) hT1 hF1
  have e3' := nonprom_nonneg y x pT pF (by linarith) (by linarith) hT1 hF1
  have e4 := prom_le y x pT pF (by linarith) (by linarith)
  have hpos : 0 ≤ pF := by linarith
  have h1 : pF * nonpromDemand y x pT pF ≤ η := by nlinarith
  have h2 : r * pT * promDemand y x pT pF ≤ r * y := by
    have : 0 ≤ promDemand y x pT pF := by
      have := prom_ge y x pT pF 1 (by linarith) (by linarith) (by linarith) (by norm_num) (by linarith)
      linarith
    have : pT * promDemand y x pT pF ≤ y := by nlinarith
    nlinarith
  have h3 : pF * (x * (1 - η)) ≤ pF * promDemand x y pF pT := mul_le_mul_of_nonneg_left e1 hpos
  have h4 : 0 ≤ r * pT * nonpromDemand x y pF pT := by
    apply mul_nonneg (mul_nonneg hr0 (by linarith)) e2
  have h5 : (1 - η) * (x * (1 - η)) < pF * (x * (1 - η)) := by
    apply mul_lt_mul_of_pos_right hF; nlinarith
  have hx : ρL ≤ x := a1
  have h6 : x * (1 - 2 * η) ≤ (1 - η) * (x * (1 - η)) := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x) (sq_nonneg η)]
  have h7 : η ≤ 1 / 10 := by linarith
  have h8 : x * η ≤ x / 10 := by nlinarith
  nlinarith

lemma sP_expand (ρH ρL r α pF pT : ℝ) (σ0 : Ranking) :
    sellerProfit ρH ρL r α σ0 pF pT = (1 - r) * pT *
      (α * typeDemand ρH ρL pF pT .f (σ0 .f) .T + (1 - α) * typeDemand ρH ρL pF pT .t (σ0 .t) .T) := by
  unfold sellerProfit demand
  rw [show (Finset.univ : Finset CType) = {CType.f, CType.t} from rfl, Finset.sum_pair (by decide)]
  simp only [mass]

lemma td_F_T (ρH ρL pF pT : ℝ) (k : CType) : typeDemand ρH ρL pF pT k .F .T =
    nonpromDemand (matchProb ρH ρL k .F) (matchProb ρH ρL k .T) pF pT := by
  simp [typeDemand, Product.other, price]

lemma td_half (ρH ρL pF : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hF0 : 0 ≤ pF) (hF1 : pF ≤ 1) (k : CType) (prom : Product) :
    ρL ^ 2 * (1 - ρH) / 2 ≤ typeDemand ρH ρL pF (1/2) k prom .T := by
  obtain ⟨a1, a2⟩ := mp_bounds ρH ρL hLH.le k .F
  obtain ⟨b1, b2⟩ := mp_bounds ρH ρL hLH.le k .T
  cases prom
  · rw [td_F_T]
    have := nonprom_half (matchProb ρH ρL k .F) (matchProb ρH ρL k .T) pF (by linarith) (by linarith) hF0 hF1
    have h1 : ρL ^ 2 ≤ (matchProb ρH ρL k .T) ^ 2 := by nlinarith
    have h2 : 1 - ρH ≤ 1 - matchProb ρH ρL k .F := by linarith
    have h3 : ρL ^ 2 * (1 - ρH) ≤ (1 - matchProb ρH ρL k .F) * (matchProb ρH ρL k .T) ^ 2 := by
      nlinarith [mul_le_mul h2 h1 (by positivity) (by linarith)]
    linarith
  · have e : typeDemand ρH ρL pF (1/2) k .T .T =
        promDemand (matchProb ρH ρL k .T) (matchProb ρH ρL k .F) (1/2) pF := by
      simp [typeDemand, Product.other, price]
    rw [e]
    have := prom_half (matchProb ρH ρL k .T) (matchProb ρH ρL k .F) pF (by linarith) (by linarith) (by linarith) hF0
    have : ρL ^ 2 * (1 - ρH) ≤ ρL := by nlinarith
    linarith

lemma ns_not_near (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hC : r * ρH ≤ 64 / 100 * ρL)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (pF pT : ℝ) (σ : ℝ → ℝ → Ranking)
    (h : IsNSEquilibrium ρH ρL r α pF pT σ) :
    pF ≤ 1 - ρL ^ 2 * (1 - ρH) / 10 ∨ pT ≤ 1 - ρL ^ 2 * (1 - ρH) / 10 := by
  obtain ⟨hopt, ⟨hF0, hF1⟩, ⟨hT0, hT1⟩, -, hTdev⟩ := h
  by_contra hc
  push Not at hc
  obtain ⟨hcF, hcT⟩ := hc
  set η := ρL ^ 2 * (1 - ρH) / 10 with hη
  have hη0 : 0 < η := by rw [hη]; have : 0 < 1 - ρH := by linarith
                         positivity
  have hη1 : η ≤ ρL / 10 := by rw [hη]; nlinarith
  have hr1 : r < 1 := by nlinarith
  have hσ : σ pF pT = fPrimeAll := by
    funext k
    have hk := hopt pF ⟨hF0, hF1⟩ pT ⟨hT0, hT1⟩ k .F
    cases hs : σ pF pT k
    · rfl
    · rw [hs] at hk
      exact absurd hk (not_le.2 (rank_F ρH ρL r pF pT η hL hLH hH hr0 hC hη0 hη1 hcF hF1 hcT hT1 k))
  have hdev := hTdev (1/2) ⟨by norm_num, by norm_num⟩
  rw [hσ, sP_expand, sP_expand] at hdev
  simp only [fPrimeAll] at hdev
  rw [td_F_T, td_F_T] at hdev
  have l1 := td_half ρH ρL pF hL hLH hH hF0 hF1 .f (σ pF (1/2) .f)
  have l2 := td_half ρH ρL pF hL hLH hH hF0 hF1 .t (σ pF (1/2) .t)
  obtain ⟨a1, a2⟩ := mp_bounds ρH ρL hLH.le .f .F
  obtain ⟨b1, b2⟩ := mp_bounds ρH ρL hLH.le .f .T
  obtain ⟨c1, c2⟩ := mp_bounds ρH ρL hLH.le .t .F
  obtain ⟨d1, d2⟩ := mp_bounds ρH ρL hLH.le .t .T
  have u1 := nonprom_le (matchProb ρH ρL .f .F) (matchProb ρH ρL .f .T) pF pT (by linarith) (by linarith) (by linarith) (by linarith) hF1 hT1
  have u2 := nonprom_le (matchProb ρH ρL .t .F) (matchProb ρH ρL .t .T) pF pT (by linarith) (by linarith) (by linarith) (by linarith) hF1 hT1
  set A := typeDemand ρH ρL pF (1/2) .f (σ pF (1/2) .f) .T
  set B := typeDemand ρH ρL pF (1/2) .t (σ pF (1/2) .t) .T
  set X := nonpromDemand (matchProb ρH ρL .f .F) (matchProb ρH ρL .f .T) pF pT
  set Y := nonpromDemand (matchProb ρH ρL .t .F) (matchProb ρH ρL .t .T) pF pT
  have hlow : ρL ^ 2 * (1 - ρH) / 2 ≤ α * A + (1 - α) * B := by nlinarith
  have hup : α * X + (1 - α) * Y ≤ 1 - pT := by nlinarith
  have hpos : 0 < 1 - r := by linarith
  have : (1 - r) * (1/2) * (ρL ^ 2 * (1 - ρH) / 2) ≤ (1 - r) * pT * (1 - pT) := by
    have e1 : (1 - r) * (1/2) * (ρL ^ 2 * (1 - ρH) / 2) ≤ (1 - r) * (1/2) * (α * A + (1 - α) * B) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    have e2 : (1 - r) * pT * (α * X + (1 - α) * Y) ≤ (1 - r) * pT * (1 - pT) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    linarith
  have : (1 - r) * pT * (1 - pT) ≤ (1 - r) * (1 - pT) := by
    have : 0 ≤ (1 - r) * (1 - pT) := mul_nonneg hpos.le (by linarith)
    nlinarith
  have : (1 - r) * (1 - pT) < (1 - r) * η := by nlinarith
  rw [hη] at this
  nlinarith

lemma cont (a : ℝ) : Continuous (fun c : ℝ => max (a - c) 0) := by fun_prop

lemma Iint (a : ℝ) (ha : a ≤ 1) :
    ∫ c in (0 : ℝ)..1, max (a - c) 0 = (max a 0) ^ 2 / 2 := by
  rcases le_or_gt a 0 with h | h
  · rw [max_eq_right h]
    have : ∫ c in (0 : ℝ)..1, max (a - c) 0 = ∫ c in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro c hc
      rw [Set.uIcc_of_le zero_le_one] at hc
      simp only
      exact max_eq_right (by linarith [hc.1])
    rw [this]
    simp
  · rw [max_eq_left h.le]
    rw [← intervalIntegral.integral_add_adjacent_intervals ((cont a).intervalIntegrable 0 a)
      ((cont a).intervalIntegrable a 1)]
    have h1 : ∫ c in (0 : ℝ)..a, max (a - c) 0 = ∫ c in (0 : ℝ)..a, (a - c) := by
      apply intervalIntegral.integral_congr
      intro c hc
      rw [Set.uIcc_of_le h.le] at hc
      simp only
      exact max_eq_left (by linarith [hc.2])
    have h2 : ∫ c in a..1, max (a - c) 0 = ∫ c in a..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro c hc
      rw [Set.uIcc_of_le ha] at hc
      simp only
      exact max_eq_right (by linarith [hc.1])
    rw [h1, h2, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
    ring

lemma Tint (ρ1 ρ2 p1 p2 : ℝ) (h1 : ρ2 * (p1 - p2) ≤ 1) (h2 : ρ2 * (1 - p2) ≤ 1) :
    ∫ c in (0 : ℝ)..1, typeSurplus ρ1 ρ2 p1 p2 c =
      ρ1 * (1 - p1) + ρ1 * ((max (ρ2 * (p1 - p2)) 0) ^ 2 / 2) +
        (1 - ρ1) * ((max (ρ2 * (1 - p2)) 0) ^ 2 / 2) := by
  unfold typeSurplus
  have i1 := (cont (ρ2 * (p1 - p2))).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have i2 := (cont (ρ2 * (1 - p2))).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [intervalIntegral.integral_add ((intervalIntegrable_const.add i1).const_mul ρ1)
    (i2.const_mul (1 - ρ1))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const i1, Iint _ h1, Iint _ h2]
  simp
  ring

lemma Jint (ρ1 ρ2 p1 p2 : ℝ) (hr2 : 0 ≤ ρ2) (hr2' : ρ2 ≤ 1) (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1)
    (hp2 : 0 ≤ p2) (hp2' : p2 ≤ 1) :
    ∫ c in (0 : ℝ)..1, typeSurplus ρ1 ρ2 p1 p2 c =
      ρ1 * (1 - p1) + ρ1 * ((max (ρ2 * (p1 - p2)) 0) ^ 2 / 2) +
        (1 - ρ1) * ((max (ρ2 * (1 - p2)) 0) ^ 2 / 2) :=
  Tint ρ1 ρ2 p1 p2 (by nlinarith) (by nlinarith)

lemma E_low (ρH ρL ρ1 ρ2 p1 p2 η : ℝ) (hL : 0 < ρL) (hH : ρH < 1)
    (a1 : ρL ≤ ρ1) (a2 : ρ1 ≤ ρH) (b1 : ρL ≤ ρ2) (b2 : ρ2 ≤ ρH)
    (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1) (hp2 : 0 ≤ p2) (hp2' : p2 ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (h : p1 ≤ 1 - η ∨ p2 ≤ 1 - η) :
    (1 - ρH) * ρL ^ 2 * η ^ 2 / 2 ≤
      ρ1 * (1 - p1) + ρ1 * ((max (ρ2 * (p1 - p2)) 0) ^ 2 / 2) +
        (1 - ρ1) * ((max (ρ2 * (1 - p2)) 0) ^ 2 / 2) := by
  have t1 : 0 ≤ ρ1 * ((max (ρ2 * (p1 - p2)) 0) ^ 2 / 2) := by
    apply mul_nonneg (by linarith); positivity
  have t2 : 0 ≤ (1 - ρ1) * ((max (ρ2 * (1 - p2)) 0) ^ 2 / 2) := by
    apply mul_nonneg (by linarith); positivity
  have t0 : 0 ≤ ρ1 * (1 - p1) := mul_nonneg (by linarith) (by linarith)
  rcases h with h | h
  · have : ρL * η ≤ ρ1 * (1 - p1) := by nlinarith
    have : (1 - ρH) * ρL ^ 2 * η ^ 2 / 2 ≤ ρL * η := by
      have : (1 - ρH) * ρL * η ≤ 1 := by
        have : ρL * η ≤ 1 := by nlinarith
        nlinarith
      nlinarith [mul_pos hL hη]
    linarith
  · have m : ρL * η ≤ max (ρ2 * (1 - p2)) 0 := by
      apply le_trans _ (le_max_left _ _); nlinarith
    have m2 : (ρL * η) ^ 2 ≤ (max (ρ2 * (1 - p2)) 0) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) m
    have : (1 - ρH) * ((ρL * η) ^ 2 / 2) ≤ (1 - ρ1) * ((max (ρ2 * (1 - p2)) 0) ^ 2 / 2) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    nlinarith

lemma E_up (ρ1 ρ2 p1 p2 ε : ℝ) (a1 : 0 ≤ ρ1) (a2 : ρ1 ≤ 1) (b1 : 0 ≤ ρ2) (b2 : ρ2 ≤ 1)
    (hp1 : 1 - ε ≤ p1) (hp1' : p1 ≤ 1) (hp2 : 1 - ε ≤ p2) (hp2' : p2 ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
      ρ1 * (1 - p1) + ρ1 * ((max (ρ2 * (p1 - p2)) 0) ^ 2 / 2) +
        (1 - ρ1) * ((max (ρ2 * (1 - p2)) 0) ^ 2 / 2) ≤ 3 * ε := by
  have m1 : max (ρ2 * (p1 - p2)) 0 ≤ ε := max_le (by nlinarith) hε
  have m2 : max (ρ2 * (1 - p2)) 0 ≤ ε := max_le (by nlinarith) hε
  have n1 : 0 ≤ max (ρ2 * (p1 - p2)) 0 := le_max_right _ _
  have n2 : 0 ≤ max (ρ2 * (1 - p2)) 0 := le_max_right _ _
  have s1 : (max (ρ2 * (p1 - p2)) 0) ^ 2 ≤ ε := by nlinarith
  have s2 : (max (ρ2 * (1 - p2)) 0) ^ 2 ≤ ε := by nlinarith
  have : ρ1 * (1 - p1) ≤ ε := by nlinarith
  have : ρ1 * ((max (ρ2 * (p1 - p2)) 0) ^ 2 / 2) ≤ ε := by nlinarith
  have : (1 - ρ1) * ((max (ρ2 * (1 - p2)) 0) ^ 2 / 2) ≤ ε := by nlinarith
  linarith

lemma cs_expand (ρH ρL α pF pT : ℝ) (σ0 : Ranking) :
    consumerSurplus ρH ρL α σ0 pF pT =
      α * (∫ c in (0 : ℝ)..1, typeSurplus (matchProb ρH ρL .f (σ0 .f)) (matchProb ρH ρL .f (σ0 .f).other)
        (price pF pT (σ0 .f)) (price pF pT (σ0 .f).other) c)
      + (1 - α) * (∫ c in (0 : ℝ)..1, typeSurplus (matchProb ρH ρL .t (σ0 .t)) (matchProb ρH ρL .t (σ0 .t).other)
        (price pF pT (σ0 .t)) (price pF pT (σ0 .t).other) c) := by
  unfold consumerSurplus
  rw [show (Finset.univ : Finset CType) = {CType.f, CType.t} from rfl, Finset.sum_pair (by decide)]
  simp only [mass]

lemma price_bounds (pF pT : ℝ) (j : Product) (lo : ℝ) (h1 : lo ≤ pF) (h2 : pF ≤ 1) (h3 : lo ≤ pT) (h4 : pT ≤ 1) :
    lo ≤ price pF pT j ∧ price pF pT j ≤ 1 := by
  cases j <;> simp [price, *]

lemma J_low (ρH ρL pF pT η : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hF0 : 0 ≤ pF) (hF1 : pF ≤ 1) (hT0 : 0 ≤ pT) (hT1 : pT ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (h : pF ≤ 1 - η ∨ pT ≤ 1 - η) (k : CType) (prom : Product) :
    (1 - ρH) * ρL ^ 2 * η ^ 2 / 2 ≤ ∫ c in (0 : ℝ)..1, typeSurplus (matchProb ρH ρL k prom)
      (matchProb ρH ρL k prom.other) (price pF pT prom) (price pF pT prom.other) c := by
  obtain ⟨a1, a2⟩ := mp_bounds ρH ρL hLH.le k prom
  obtain ⟨b1, b2⟩ := mp_bounds ρH ρL hLH.le k prom.other
  obtain ⟨c1, c2⟩ := price_bounds pF pT prom 0 hF0 hF1 hT0 hT1
  obtain ⟨d1, d2⟩ := price_bounds pF pT prom.other 0 hF0 hF1 hT0 hT1
  rw [Jint _ _ _ _ (by linarith) (by linarith) c1 c2 d1 d2]
  apply E_low ρH ρL _ _ _ _ η hL hH a1 a2 b1 b2 c1 c2 d1 d2 hη hη1
  cases prom <;> simp only [price, Product.other] <;> tauto

lemma J_up (ρH ρL pF pT ε : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hF0 : 1 - ε ≤ pF) (hF1 : pF ≤ 1) (hT0 : 1 - ε ≤ pT) (hT1 : pT ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (k : CType) (prom : Product) :
    ∫ c in (0 : ℝ)..1, typeSurplus (matchProb ρH ρL k prom)
      (matchProb ρH ρL k prom.other) (price pF pT prom) (price pF pT prom.other) c ≤ 3 * ε := by
  obtain ⟨a1, a2⟩ := mp_bounds ρH ρL hLH.le k prom
  obtain ⟨b1, b2⟩ := mp_bounds ρH ρL hLH.le k prom.other
  obtain ⟨c1, c2⟩ := price_bounds pF pT prom _ hF0 hF1 hT0 hT1
  obtain ⟨d1, d2⟩ := price_bounds pF pT prom.other _ hF0 hF1 hT0 hT1
  rw [Jint _ _ _ _ (by linarith) (by linarith) (by linarith) c2 (by linarith) d2]
  exact E_up _ _ _ _ ε (by linarith) (by linarith) (by linarith) (by linarith) c1 c2 d1 d2 hε hε1

/-- Seller `T`'s first-order condition on `[p_F, 1]` under the neutral ranking. -/
lemma TFOC (ρH ρL r α pF pT : ℝ) (hr' : r < 1)
    (hN : 0 < ρL ^ 2 * ((1 - α) * ρH + α * (1 - ρH)))
    (hF0 : 0 ≤ pF) (hle : pF ≤ pT) (hT1 : pT < 1)
    (hTdev : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      sellerProfit ρH ρL r α neutral pF q ≤ sellerProfit ρH ρL r α neutral pF pT) :
    (1 - α) * ρH * (1 + ρL ^ 2 * pF) + α * (1 - ρH) * ρL ^ 2 ≤
      2 * (ρL ^ 2 * ((1 - α) * ρH + α * (1 - ρH))) * pT := by
  by_contra h
  push Not at h
  set N := ρL ^ 2 * ((1 - α) * ρH + α * (1 - ρH)) with hNdef
  set KT := (1 - α) * ρH * (1 + ρL ^ 2 * pF) + α * (1 - ρH) * ρL ^ 2 with hKT
  set q := min 1 (KT / (2 * N)) with hq
  have hq1 : q ≤ 1 := min_le_left _ _
  have hq2 : q ≤ KT / (2 * N) := min_le_right _ _
  have hpq : pT < q := lt_min hT1 ((lt_div_iff₀ (by positivity)).2 (by linarith))
  have hdev := hTdev q ⟨by linarith, hq1⟩
  rw [sT_high _ _ _ _ _ _ (by linarith : pF ≤ q), sT_high _ _ _ _ _ _ hle] at hdev
  have h2 : 2 * N * q ≤ KT := by
    have := (le_div_iff₀ (by positivity)).1 hq2; linarith
  have e : (1 - r) * q * ((1 - α) * ρH * (1 - ρL ^ 2 * (q - pF)) + α * (1 - ρH) * ρL ^ 2 * (1 - q)) -
      (1 - r) * pT * ((1 - α) * ρH * (1 - ρL ^ 2 * (pT - pF)) + α * (1 - ρH) * ρL ^ 2 * (1 - pT)) =
      (1 - r) * (q - pT) * (KT - N * (q + pT)) := by rw [hKT, hNdef]; ring
  have h3 : N * pT < N * q := mul_lt_mul_of_pos_left hpq hN
  have : 0 < (1 - r) * (q - pT) * (KT - N * (q + pT)) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  linarith

/-- The platform's first-order condition on `[0, p_T]` under the neutral ranking. -/
lemma FFOC (ρH ρL r α pF pT : ℝ) (hM : 0 < (1 - α) * ρL ^ 2)
    (hF0 : 0 ≤ pF) (hlt : pF < pT) (hT1 : pT ≤ 1)
    (hFdev : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      platformProfit ρH ρL r α neutral q pT ≤ platformProfit ρH ρL r α neutral pF pT) :
    r * pT * (1 - α) * ρH * ρL ^ 2 + α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT) ≤
      2 * ((1 - α) * ρL ^ 2) * pF := by
  by_contra h
  push Not at h
  set M := (1 - α) * ρL ^ 2 with hMdef
  set K := r * pT * (1 - α) * ρH * ρL ^ 2 + α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT) with hK
  set q := min pT (K / (2 * M)) with hq
  have hq1 : q ≤ pT := min_le_left _ _
  have hq2 : q ≤ K / (2 * M) := min_le_right _ _
  have hpq : pF < q := lt_min hlt ((lt_div_iff₀ (by positivity)).2 (by linarith))
  have hdev := hFdev q ⟨by linarith, by linarith⟩
  rw [sF_low _ _ _ _ _ _ hq1, sF_low _ _ _ _ _ _ hlt.le] at hdev
  have h2 : 2 * M * q ≤ K := by
    have := (le_div_iff₀ (by positivity)).1 hq2; linarith
  have e : q * (α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT - q)) +
        r * pT * (α * (1 - ρH) * ρL ^ 2 * (1 - pT) + (1 - α) * ρH * (1 - ρL ^ 2 * pT + ρL ^ 2 * q)) -
      (pF * (α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT - pF)) +
        r * pT * (α * (1 - ρH) * ρL ^ 2 * (1 - pT) + (1 - α) * ρH * (1 - ρL ^ 2 * pT + ρL ^ 2 * pF))) =
      (q - pF) * (K - M * (q + pF)) := by rw [hK, hMdef]; ring
  have h3 : M * pF < M * q := mul_lt_mul_of_pos_left hpq hM
  have : 0 < (q - pF) * (K - M * (q + pF)) := mul_pos (by linarith) (by linarith)
  linarith

/-- Region `α ≤ 1/2`: every equilibrium with neutrality has `p_T = 1` and `p_F ≥ 1 - ε`. -/
lemma regionI (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr' : r < 1) (α : ℝ) (hα0 : 0 ≤ α) (hαh : α ≤ 1 / 2) (ε : ℝ) (hε0 : 0 < ε)
    (C1 : (1 - ε) * ((1 - α) * ρL ^ 2 * (2 - ρH * (1 + r))) ≤ α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH))
    (C2 : 2 * (ρL ^ 2 * ((1 - α) * ρH + α * (1 - ρH))) <
      (1 - α) * ρH * (1 + ρL ^ 2 * (1 - ε)) + α * (1 - ρH) * ρL ^ 2)
    (pF pT : ℝ) (heq : IsSEquilibrium ρH ρL r α pF pT) : 1 - ε ≤ pF ∧ pT = 1 := by
  obtain ⟨⟨hF0, hF1⟩, ⟨hT0, hT1⟩, hFdev, hTdev⟩ := heq
  have hρ2 : ρL ^ 2 < ρH := by nlinarith
  have h1α : 0 < 1 - α := by linarith
  have hM : 0 < (1 - α) * ρL ^ 2 := by positivity
  have hN : 0 < ρL ^ 2 * ((1 - α) * ρH + α * (1 - ρH)) := by
    have : 0 < (1 - α) * ρH := by nlinarith
    have : 0 ≤ α * (1 - ρH) := mul_nonneg hα0 (by linarith)
    positivity
  have hr1 : 0 < 1 - r := by linarith
  have hα2 : α * ρL ^ 2 ≥ 0 := by positivity
  -- Step 1: p_F ≤ p_T
  have hle : pF ≤ pT := by
    by_contra hlt
    push Not at hlt
    have h := hTdev pF ⟨hF0, hF1⟩
    rw [sT_low _ _ _ _ _ _ le_rfl, sT_low _ _ _ _ _ _ hlt.le] at h
    have hX : -1 ≤ 1 - ρH + ρH * pF - pF - pT := by nlinarith
    have hB : 0 < (1 - α) * ρH + α * ρL ^ 2 * (1 - ρH + ρH * pF - pF - pT) := by
      have := mul_le_mul_of_nonneg_left hX hα2
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 2 - α) (by nlinarith : (0:ℝ) ≤ ρH + ρL ^ 2)]
    have e : (1 - r) * pF * ((1 - α) * ρH + α * (ρL ^ 2 * (1 - ρH + ρH * pF - pF))) -
        (1 - r) * pT * ((1 - α) * ρH + α * (ρL ^ 2 * (1 - ρH + ρH * pF - pT))) =
        (1 - r) * (pF - pT) * ((1 - α) * ρH + α * ρL ^ 2 * (1 - ρH + ρH * pF - pF - pT)) := by ring
    have : 0 < (1 - r) * (pF - pT) * ((1 - α) * ρH + α * ρL ^ 2 * (1 - ρH + ρH * pF - pF - pT)) :=
      mul_pos (mul_pos hr1 (by linarith)) hB
    linarith
  have hc : 0 ≤ (1 - α) * ρL ^ 2 * ρH * (1 + r) :=
    mul_nonneg (mul_nonneg hM.le (by linarith)) (by linarith)
  have h2M : 0 < (1 - α) * ρL ^ 2 * (2 - ρH * (1 + r)) := by
    apply mul_pos hM; nlinarith
  -- Step 2: p_T = 1
  have hT : pT = 1 := by
    by_contra hne
    have hT1' : pT < 1 := lt_of_le_of_ne hT1 hne
    have hfoc := TFOC ρH ρL r α pF pT hr' hN hF0 hle hT1' hTdev
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hffoc := FFOC ρH ρL r α pF pT hM hF0 hlt hT1 hFdev
      -- p_F ≥ 1 - ε
      have hcc := mul_le_mul_of_nonneg_left hle hc
      have hK : r * pF * (1 - α) * ρH * ρL ^ 2 + α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pF) ≤
          r * pT * (1 - α) * ρH * ρL ^ 2 + α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT) := by
        linarith
      have hpF : (1 - ε) * ((1 - α) * ρL ^ 2 * (2 - ρH * (1 + r))) ≤
          pF * ((1 - α) * ρL ^ 2 * (2 - ρH * (1 + r))) := by linarith
      have hpF' : 1 - ε ≤ pF := le_of_mul_le_mul_right hpF h2M
      have hq : 1 + ρL ^ 2 * (1 - ε) ≤ 1 + ρL ^ 2 * pF := by
        have := mul_le_mul_of_nonneg_left hpF' (sq_nonneg ρL); linarith
      have : (1 - α) * ρH * (1 + ρL ^ 2 * (1 - ε)) ≤ (1 - α) * ρH * (1 + ρL ^ 2 * pF) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg h1α.le (by linarith))
      have : 2 * (ρL ^ 2 * ((1 - α) * ρH + α * (1 - ρH))) * pT <
          2 * (ρL ^ 2 * ((1 - α) * ρH + α * (1 - ρH))) * 1 :=
        mul_lt_mul_of_pos_left hT1' (by linarith)
      linarith
    · subst heq
      have hcoef : 0 < (1 - α) * ρH * ρL ^ 2 + 2 * α * (1 - ρH) * ρL ^ 2 := by
        have : 0 ≤ α * (1 - ρH) * ρL ^ 2 := by
          apply mul_nonneg (mul_nonneg hα0 (by linarith)) (sq_nonneg _)
        have := mul_pos (mul_pos h1α (by linarith : (0:ℝ) < ρH)) (by positivity : (0:ℝ) < ρL ^ 2)
        linarith
      have hg : 0 ≤ (1 - α) * ρH * (1 - ρL ^ 2) - α * (1 - ρH) * ρL ^ 2 := by
        have a : α * (ρH * (1 - ρL ^ 2)) ≤ (1 - α) * (ρH * (1 - ρL ^ 2)) := by
          apply mul_le_mul_of_nonneg_right (by linarith); nlinarith
        have b : α * ((1 - ρH) * ρL ^ 2) ≤ α * (ρH * (1 - ρL ^ 2)) := by
          apply mul_le_mul_of_nonneg_left (by nlinarith) hα0
        nlinarith
      have := mul_lt_mul_of_pos_left hT1' hcoef
      linarith
  refine ⟨?_, hT⟩
  subst hT
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hffoc := FFOC ρH ρL r α pF 1 hM hF0 hlt le_rfl hFdev
    have hec := mul_nonneg hε0.le hc
    have : (1 - ε) * (2 * ((1 - α) * ρL ^ 2)) ≤ 2 * ((1 - α) * ρL ^ 2) * pF := by linarith
    rw [mul_comm] at this
    exact le_of_mul_le_mul_left this (by linarith)
  · linarith

/-- The platform's first-order condition on `[p_T, 1]` under the neutral ranking. -/
lemma FFOC2 (ρH ρL r α pF pT : ℝ)
    (hN : 0 < ρL ^ 2 * (α * ρH + (1 - α) * (1 - ρH)))
    (hT0 : 0 ≤ pT) (hle : pT ≤ pF) (hF1 : pF < 1)
    (hFdev : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      platformProfit ρH ρL r α neutral q pT ≤ platformProfit ρH ρL r α neutral pF pT) :
    α * ρH * (1 + ρL ^ 2 * pT) + (1 - α) * (1 - ρH) * ρL ^ 2 + r * pT * α * ρL ^ 2 * ρH ≤
      2 * (ρL ^ 2 * (α * ρH + (1 - α) * (1 - ρH))) * pF := by
  by_contra h
  push Not at h
  set N := ρL ^ 2 * (α * ρH + (1 - α) * (1 - ρH)) with hNdef
  set K := α * ρH * (1 + ρL ^ 2 * pT) + (1 - α) * (1 - ρH) * ρL ^ 2 + r * pT * α * ρL ^ 2 * ρH with hK
  set q := min 1 (K / (2 * N)) with hq
  have hq1 : q ≤ 1 := min_le_left _ _
  have hq2 : q ≤ K / (2 * N) := min_le_right _ _
  have hpq : pF < q := lt_min hF1 ((lt_div_iff₀ (by positivity)).2 (by linarith))
  have hdev := hFdev q ⟨by linarith, hq1⟩
  rw [sF_high _ _ _ _ _ _ (by linarith : pT ≤ q), sF_high _ _ _ _ _ _ hle] at hdev
  have h2 : 2 * N * q ≤ K := by
    have := (le_div_iff₀ (by positivity)).1 hq2; linarith
  have e : q * (α * ρH * (1 - ρL ^ 2 * (q - pT)) + (1 - α) * (1 - ρH) * ρL ^ 2 * (1 - q)) +
        r * pT * (α * ρL ^ 2 * (1 - ρH + ρH * q - pT) + (1 - α) * ρH) -
      (pF * (α * ρH * (1 - ρL ^ 2 * (pF - pT)) + (1 - α) * (1 - ρH) * ρL ^ 2 * (1 - pF)) +
        r * pT * (α * ρL ^ 2 * (1 - ρH + ρH * pF - pT) + (1 - α) * ρH)) =
      (q - pF) * (K - N * (q + pF)) := by rw [hK, hNdef]; ring
  have h3 : N * pF < N * q := mul_lt_mul_of_pos_left hpq hN
  have : 0 < (q - pF) * (K - N * (q + pF)) := mul_pos (by linarith) (by linarith)
  linarith

/-- Seller `T`'s first-order condition on `[0, p_F]` under the neutral ranking. -/
lemma TFOC2 (ρH ρL r α pF pT : ℝ) (hr' : r < 1) (hM : 0 < α * ρL ^ 2)
    (hT0 : 0 ≤ pT) (hlt : pT < pF) (hF1 : pF ≤ 1)
    (hTdev : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      sellerProfit ρH ρL r α neutral pF q ≤ sellerProfit ρH ρL r α neutral pF pT) :
    α * ρL ^ 2 * (1 - ρH + ρH * pF) + (1 - α) * ρH ≤ 2 * (α * ρL ^ 2) * pT := by
  by_contra h
  push Not at h
  set M := α * ρL ^ 2 with hMdef
  set K := α * ρL ^ 2 * (1 - ρH + ρH * pF) + (1 - α) * ρH with hK
  set q := min pF (K / (2 * M)) with hq
  have hq1 : q ≤ pF := min_le_left _ _
  have hq2 : q ≤ K / (2 * M) := min_le_right _ _
  have hpq : pT < q := lt_min hlt ((lt_div_iff₀ (by positivity)).2 (by linarith))
  have hdev := hTdev q ⟨by linarith, by linarith⟩
  rw [sT_low _ _ _ _ _ _ hq1, sT_low _ _ _ _ _ _ hlt.le] at hdev
  have h2 : 2 * M * q ≤ K := by
    have := (le_div_iff₀ (by positivity)).1 hq2; linarith
  have e : (1 - r) * q * ((1 - α) * ρH + α * (ρL ^ 2 * (1 - ρH + ρH * pF - q))) -
      (1 - r) * pT * ((1 - α) * ρH + α * (ρL ^ 2 * (1 - ρH + ρH * pF - pT))) =
      (1 - r) * (q - pT) * (K - M * (q + pT)) := by rw [hK, hMdef]; ring
  have h3 : M * pT < M * q := mul_lt_mul_of_pos_left hpq hM
  have : 0 < (1 - r) * (q - pT) * (K - M * (q + pT)) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  linarith

/-- Region `α > 1/2`: every equilibrium with neutrality has `p_F = 1` and `p_T ≥ 1 - ε`. -/
lemma regionII (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr' : r < 1) (α : ℝ) (hαh : 1 / 2 < α) (hα1 : α ≤ 1) (ε : ℝ) (hε0 : 0 < ε)
    (C1 : (1 - ε) * (α * ρL ^ 2 * (2 - ρH)) ≤ α * ρL ^ 2 * (1 - ρH) + (1 - α) * ρH)
    (C2 : 2 * (ρL ^ 2 * (α * ρH + (1 - α) * (1 - ρH))) <
      α * ρH * (1 + ρL ^ 2 * (1 - ε)) + (1 - α) * (1 - ρH) * ρL ^ 2)
    (pF pT : ℝ) (heq : IsSEquilibrium ρH ρL r α pF pT) : pF = 1 ∧ 1 - ε ≤ pT := by
  obtain ⟨⟨hF0, hF1⟩, ⟨hT0, hT1⟩, hFdev, hTdev⟩ := heq
  have hρ2 : ρL ^ 2 < ρH := by nlinarith
  have hα0 : 0 < α := by linarith
  have h1α : 0 ≤ 1 - α := by linarith
  have hM : 0 < α * ρL ^ 2 := by positivity
  have hN : 0 < ρL ^ 2 * (α * ρH + (1 - α) * (1 - ρH)) := by
    have : 0 < α * ρH := by nlinarith
    have : 0 ≤ (1 - α) * (1 - ρH) := mul_nonneg h1α (by linarith)
    have : 0 < α * ρH + (1 - α) * (1 - ρH) := by linarith
    positivity
  have hM1 : 0 ≤ (1 - α) * ρL ^ 2 := mul_nonneg h1α (sq_nonneg _)
  -- Step 1: p_T ≤ p_F
  have hle : pT ≤ pF := by
    by_contra hlt
    push Not at hlt
    have h := hFdev pT ⟨hT0, hT1⟩
    rw [sF_low _ _ _ _ _ _ le_rfl, sF_low _ _ _ _ _ _ hlt.le] at h
    have hX : -1 ≤ 1 - ρH + ρH * pT - pT - pF := by nlinarith
    have hrr : 0 ≤ r * pT * (1 - α) * ρH * ρL ^ 2 := by
      apply mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hr0 hT0) h1α) (by linarith)) (sq_nonneg _)
    have hB : 0 < r * pT * (1 - α) * ρH * ρL ^ 2 + α * ρH +
        (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT - pT - pF) := by
      have := mul_le_mul_of_nonneg_left hX hM1
      have : (1 - α) * ρL ^ 2 ≤ α * ρL ^ 2 := by nlinarith
      have : α * ρL ^ 2 < α * ρH := mul_lt_mul_of_pos_left hρ2 hα0
      linarith
    have e : pT * (α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT - pT)) +
          r * pT * (α * (1 - ρH) * ρL ^ 2 * (1 - pT) + (1 - α) * ρH * (1 - ρL ^ 2 * pT + ρL ^ 2 * pT)) -
        (pF * (α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT - pF)) +
          r * pT * (α * (1 - ρH) * ρL ^ 2 * (1 - pT) + (1 - α) * ρH * (1 - ρL ^ 2 * pT + ρL ^ 2 * pF))) =
        (pT - pF) * (r * pT * (1 - α) * ρH * ρL ^ 2 + α * ρH +
          (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT - pT - pF)) := by ring
    have : 0 < (pT - pF) * (r * pT * (1 - α) * ρH * ρL ^ 2 + α * ρH +
        (1 - α) * ρL ^ 2 * (1 - ρH + ρH * pT - pT - pF)) := mul_pos (by linarith) hB
    linarith
  have h2M : 0 < α * ρL ^ 2 * (2 - ρH) := mul_pos hM (by linarith)
  have hc : 0 ≤ α * ρL ^ 2 * ρH := mul_nonneg hM.le (by linarith)
  -- Step 2: p_F = 1
  have hF : pF = 1 := by
    by_contra hne
    have hF1' : pF < 1 := lt_of_le_of_ne hF1 hne
    have hfoc := FFOC2 ρH ρL r α pF pT hN hT0 hle hF1' hFdev
    have hrt : 0 ≤ r * pT * α * ρL ^ 2 * ρH := by
      apply mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hr0 hT0) hα0.le) (sq_nonneg _)) (by linarith)
    rcases lt_or_eq_of_le hle with hlt | heq
    · have htfoc := TFOC2 ρH ρL r α pF pT hr' hM hT0 hlt hF1 hTdev
      have hcc := mul_le_mul_of_nonneg_left hle hc
      have hpT : (1 - ε) * (α * ρL ^ 2 * (2 - ρH)) ≤ pT * (α * ρL ^ 2 * (2 - ρH)) := by linarith
      have hpT' : 1 - ε ≤ pT := le_of_mul_le_mul_right hpT h2M
      have hq : 1 + ρL ^ 2 * (1 - ε) ≤ 1 + ρL ^ 2 * pT := by
        have := mul_le_mul_of_nonneg_left hpT' (sq_nonneg ρL); linarith
      have : α * ρH * (1 + ρL ^ 2 * (1 - ε)) ≤ α * ρH * (1 + ρL ^ 2 * pT) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hα0.le (by linarith))
      have : 2 * (ρL ^ 2 * (α * ρH + (1 - α) * (1 - ρH))) * pF <
          2 * (ρL ^ 2 * (α * ρH + (1 - α) * (1 - ρH))) * 1 :=
        mul_lt_mul_of_pos_left hF1' (by linarith)
      linarith
    · subst heq
      have hcoef : 0 < α * ρH * ρL ^ 2 * (1 - r) + 2 * (1 - α) * (1 - ρH) * ρL ^ 2 := by
        have : 0 ≤ (1 - α) * (1 - ρH) * ρL ^ 2 := by
          apply mul_nonneg (mul_nonneg h1α (by linarith)) (sq_nonneg _)
        have := mul_pos (mul_pos (mul_pos hα0 (by linarith : (0:ℝ) < ρH)) (by positivity : (0:ℝ) < ρL ^ 2)) (by linarith : (0:ℝ) < 1 - r)
        linarith
      have hg : α * ρH * ρL ^ 2 * (1 - r) + (1 - α) * (1 - ρH) * ρL ^ 2 ≤ α * ρH := by
        have a : (1 - α) * ((1 - ρH) * ρL ^ 2) ≤ α * ((1 - ρH) * ρL ^ 2) := by
          apply mul_le_mul_of_nonneg_right (by linarith); nlinarith
        have b : α * ((1 - ρH) * ρL ^ 2) ≤ α * (ρH * (1 - ρL ^ 2)) := by
          apply mul_le_mul_of_nonneg_left (by nlinarith) hα0.le
        have c : 0 ≤ α * ρH * ρL ^ 2 * r := by
          apply mul_nonneg (mul_nonneg (mul_nonneg hα0.le (by linarith)) (sq_nonneg _)) hr0
        linarith
      have := mul_lt_mul_of_pos_left hF1' hcoef
      linarith
  refine ⟨hF, ?_⟩
  subst hF
  rcases lt_or_eq_of_le hle with hlt | heq
  · have htfoc := TFOC2 ρH ρL r α 1 pT hr' hM hT0 hlt le_rfl hTdev
    have hec := mul_nonneg hε0.le hc
    have : (1 - ε) * (2 * (α * ρL ^ 2)) ≤ 2 * (α * ρL ^ 2) * pT := by linarith
    rw [mul_comm] at this
    exact le_of_mul_le_mul_left this (by linarith)
  · linarith

end Aux_SN31


open Aux_SN31 in
open SearchNeutrality.ShortTerm in
theorem solution (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hC : Condition1 ρH ρL r) :
    ∃ αlo αhi : ℝ,
      αlo < ρL ^ 2 * (1 - r * ρH) / (ρL ^ 2 * (1 - r * ρH) + ρH) ∧
      ρL ^ 2 * (1 - r * ρH) / (ρL ^ 2 * (1 - r * ρH) + ρH) < 1 / 2 ∧
      1 / 2 < ρH / (ρH + ρL ^ 2) ∧ ρH / (ρH + ρL ^ 2) < αhi ∧
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 → αlo < α → α < αhi →
        ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r α pF pT σ →
        ∀ qF qT : ℝ, IsSEquilibrium ρH ρL r α qF qT →
          consumerSurplus ρH ρL α neutral qF qT < consumerSurplus ρH ρL α (σ pF pT) pF pT := by
  obtain ⟨hC1, -⟩ := hC
  have hH0 : 0 < ρH := by linarith
  have hrH : r * ρH ≤ 64 / 100 * ρL := by
    have := (le_div_iff₀ hH0).1 hC1; linarith
  have hr' : r < 1 := by nlinarith
  have hρ2 : ρL ^ 2 < ρH := by nlinarith
  have h1H : 0 < 1 - ρH := by linarith
  have hrH1 : r * ρH < 1 := by nlinarith
  set η := ρL ^ 2 * (1 - ρH) / 10 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη]; have : ρL ^ 2 * (1 - ρH) ≤ 1 := by nlinarith
    linarith
  set δ := (1 - ρH) * ρL ^ 2 * η ^ 2 / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set ε := min (δ / 4) ((ρH - ρL ^ 2) / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by linarith)
  have hεδ : ε ≤ δ / 4 := min_le_left _ _
  have hερ : ε ≤ (ρH - ρL ^ 2) / 2 := min_le_right _ _
  have hε1 : ε ≤ 1 := by nlinarith [sq_nonneg ρL]
  set D := ρL ^ 2 * (1 - r * ρH) + ρH with hD
  have hDpos : 0 < D := by
    have : 0 < ρL ^ 2 * (1 - r * ρH) := mul_pos (by positivity) (by linarith)
    linarith
  set E := ρH + ρL ^ 2 with hE
  have hEpos : 0 < E := by positivity
  set t := ε * ρL ^ 2 * (1 - ρH) / 2 with ht
  have htpos : 0 < t := by positivity
  refine ⟨(ρL ^ 2 * (1 - r * ρH) - t) / D, (ρH + ε * ρL ^ 2 / 2) / E, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_lt_div_of_pos_right (by linarith) hDpos
  · rw [div_lt_iff₀ hDpos]
    have : ρL ^ 2 * (1 - r * ρH) < ρH := by
      have : ρL ^ 2 * (1 - r * ρH) ≤ ρL ^ 2 := by
        have : 0 ≤ ρL ^ 2 * (r * ρH) := by positivity
        nlinarith
      linarith
    linarith
  · rw [lt_div_iff₀ hEpos]; linarith
  · apply div_lt_div_of_pos_right _ hEpos
    have : 0 < ε * ρL ^ 2 / 2 := by positivity
    linarith
  intro α hα0 hα1 hlo hhi pF pT σ hNS qF qT hS
  -- lower bound on consumer surplus without neutrality
  have hNSlow : δ ≤ consumerSurplus ρH ρL α (σ pF pT) pF pT := by
    have hb := hNS
    obtain ⟨-, ⟨hF0, hF1⟩, ⟨hT0, hT1⟩, -, -⟩ := hb
    have hnn := ns_not_near ρH ρL r hL hLH hH hr0 hrH α hα0 hα1 pF pT σ hNS
    rw [cs_expand]
    have j1 := J_low ρH ρL pF pT η hL hLH hH hF0 hF1 hT0 hT1 hη0 hη1 hnn .f (σ pF pT .f)
    have j2 := J_low ρH ρL pF pT η hL hLH hH hF0 hF1 hT0 hT1 hη0 hη1 hnn .t (σ pF pT .t)
    have := mul_le_mul_of_nonneg_left j1 hα0
    have := mul_le_mul_of_nonneg_left j2 (by linarith : (0:ℝ) ≤ 1 - α)
    linarith
  -- prices with neutrality are close to 1
  have hq : 1 - ε ≤ qF ∧ qF ≤ 1 ∧ 1 - ε ≤ qT ∧ qT ≤ 1 := by
    have hb := hS
    obtain ⟨⟨-, hF1⟩, ⟨-, hT1⟩, -, -⟩ := hb
    rcases le_or_gt α (1 / 2) with hα | hα
    · have C1 : (1 - ε) * ((1 - α) * ρL ^ 2 * (2 - ρH * (1 + r))) ≤
          α * ρH + (1 - α) * ρL ^ 2 * (1 - ρH) := by
        have h1 : ρL ^ 2 * (1 - r * ρH) - t < α * D := by
          have := (div_lt_iff₀ hDpos).1 hlo; linarith
        have h2 : ε * (1 / 2) * ρL ^ 2 * (1 - ρH) ≤ ε * (1 - α) * ρL ^ 2 * (2 - ρH * (1 + r)) := by
          have a : 1 / 2 ≤ 1 - α := by linarith
          have b : 1 - ρH ≤ 2 - ρH * (1 + r) := by linarith
          have : (1 / 2) * (1 - ρH) ≤ (1 - α) * (2 - ρH * (1 + r)) :=
            mul_le_mul a b h1H.le (by linarith)
          have := mul_le_mul_of_nonneg_left this (mul_nonneg hε0.le (sq_nonneg ρL))
          linarith
        rw [hD] at h1; rw [ht] at h1
        linarith
      have C2 : 2 * (ρL ^ 2 * ((1 - α) * ρH + α * (1 - ρH))) <
          (1 - α) * ρH * (1 + ρL ^ 2 * (1 - ε)) + α * (1 - ρH) * ρL ^ 2 := by
        have hX : (1 - ρH) * ρL ^ 2 < ρH * (1 - ρL ^ 2 - ρL ^ 2 * ε) := by
          have : ρH * ρL ^ 2 * ε < ε := by
            have h3 : ρL ^ 2 < 1 := by linarith
            have h4 := mul_lt_mul_of_pos_left h3 hH0
            have h5 : ρH * ρL ^ 2 < 1 := by linarith
            have := mul_lt_mul_of_pos_right h5 hε0
            linarith
          linarith
        have hX0 : 0 ≤ (1 - ρH) * ρL ^ 2 := by positivity
        have a : (1 / 2) * (ρH * (1 - ρL ^ 2 - ρL ^ 2 * ε)) ≤ (1 - α) * (ρH * (1 - ρL ^ 2 - ρL ^ 2 * ε)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have b : α * ((1 - ρH) * ρL ^ 2) ≤ (1 / 2) * ((1 - ρH) * ρL ^ 2) :=
          mul_le_mul_of_nonneg_right hα hX0
        linarith
      obtain ⟨h1, h2⟩ := regionI ρH ρL r hL hLH hH hr0 hr' α hα0 hα ε hε0 C1 C2 qF qT hS
      exact ⟨h1, hF1, by rw [h2]; linarith, hT1⟩
    · have C1 : (1 - ε) * (α * ρL ^ 2 * (2 - ρH)) ≤ α * ρL ^ 2 * (1 - ρH) + (1 - α) * ρH := by
        have h1 : α * E < ρH + ε * ρL ^ 2 / 2 := by
          have := (lt_div_iff₀ hEpos).1 hhi; linarith
        have h2 : ε * (1 / 2) * ρL ^ 2 * 1 ≤ ε * α * ρL ^ 2 * (2 - ρH) := by
          have : (1 / 2) * 1 ≤ α * (2 - ρH) := mul_le_mul hα.le (by linarith) (by norm_num) (by linarith)
          have := mul_le_mul_of_nonneg_left this (mul_nonneg hε0.le (sq_nonneg ρL))
          linarith
        rw [hE] at h1
        linarith
      have C2 : 2 * (ρL ^ 2 * (α * ρH + (1 - α) * (1 - ρH))) <
          α * ρH * (1 + ρL ^ 2 * (1 - ε)) + (1 - α) * (1 - ρH) * ρL ^ 2 := by
        have hX : (1 - ρH) * ρL ^ 2 < ρH * (1 - ρL ^ 2 - ρL ^ 2 * ε) := by
          have : ρH * ρL ^ 2 * ε < ε := by
            have h3 : ρL ^ 2 < 1 := by linarith
            have h4 := mul_lt_mul_of_pos_left h3 hH0
            have h5 : ρH * ρL ^ 2 < 1 := by linarith
            have := mul_lt_mul_of_pos_right h5 hε0
            linarith
          linarith
        have hX0 : 0 ≤ (1 - ρH) * ρL ^ 2 := by positivity
        have a : (1 / 2) * (ρH * (1 - ρL ^ 2 - ρL ^ 2 * ε)) ≤ α * (ρH * (1 - ρL ^ 2 - ρL ^ 2 * ε)) :=
          mul_le_mul_of_nonneg_right hα.le (by linarith)
        have b : (1 - α) * ((1 - ρH) * ρL ^ 2) ≤ (1 / 2) * ((1 - ρH) * ρL ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hX0
        linarith
      obtain ⟨h1, h2⟩ := regionII ρH ρL r hL hLH hH hr0 hr' α hα hα1 ε hε0 C1 C2 qF qT hS
      exact ⟨by rw [h1]; linarith, hF1, h2, hT1⟩
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  have hSup : consumerSurplus ρH ρL α neutral qF qT ≤ 3 * ε := by
    rw [cs_expand]
    have j1 := J_up ρH ρL qF qT ε hL hLH hH hq1 hq2 hq3 hq4 hε0.le hε1 .f (neutral .f)
    have j2 := J_up ρH ρL qF qT ε hL hLH hH hq1 hq2 hq3 hq4 hε0.le hε1 .t (neutral .t)
    have := mul_le_mul_of_nonneg_left j1 hα0
    have := mul_le_mul_of_nonneg_left j2 (by linarith : (0:ℝ) ≤ 1 - α)
    linarith
  linarith
