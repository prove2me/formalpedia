-- Prove2me | solution 1 for SearchNeutrality.Commission.proposition_4_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-03T20:34:01.498991+00:00
-- url     : https://prove2.me/submissions/8845ff3d-7f0a-49ef-9aa4-d109d11a86bc

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model

open SearchNeutrality.Commission

namespace SNP5Disproof

lemma sumC (g : CType → ℝ) : ∑ k : CType, g k = g .f + g .t := by
  rw [show (Finset.univ : Finset CType) = {.f, .t} from rfl]
  rw [Finset.sum_pair (by decide)]

/-- The parameters of the counterexample. -/
noncomputable abbrev hH : ℝ := 1 / 2
noncomputable abbrev hL : ℝ := 12 / 25
noncomputable abbrev rr : ℝ := 99 / 100
noncomputable abbrev qs : ℝ := 22289 / 30025

/-- A pointwise-optimal ranking rule (ties to `F`). -/
noncomputable def σopt (ρH ρL r : ℝ) : ℝ → ℝ → Ranking := fun pF pT k =>
  if platformTypeProfit ρH ρL r pF pT k .F < platformTypeProfit ρH ρL r pF pT k .T then .T
  else .F

lemma σopt_opt (ρH ρL r : ℝ) : IsOptimalRankingRule ρH ρL r (σopt ρH ρL r) := by
  intro pF _ pT _ k prom
  unfold σopt
  split_ifs with h <;> cases prom <;> simp_all [not_lt] <;> linarith

lemma pp_eq (ρH ρL r α : ℝ) (σ : Ranking) (pF pT : ℝ) :
    platformProfit ρH ρL r α σ pF pT
      = mass α .f * platformTypeProfit ρH ρL r pF pT .f (σ .f)
        + mass α .t * platformTypeProfit ρH ρL r pF pT .t (σ .t) := by
  simp only [platformProfit, platformTypeProfit, demand, sumC]
  ring

lemma σ_at : σopt hH hL rr qs 1 = fun _ => .T := by
  funext k
  cases k <;>
  · simp only [σopt, platformTypeProfit, typeDemand, promDemand, nonpromDemand, matchProb,
      price, Product.other, reduceCtorEq, if_true, if_false]
    norm_num

lemma plat_bound (σ : Ranking) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    platformProfit hH hL rr (1 / 2) σ q 1 ≤ platformProfit hH hL rr (1 / 2) (fun _ => .T) qs 1 := by
  rw [pp_eq, pp_eq]
  simp only [mass, platformTypeProfit, typeDemand, promDemand, nonpromDemand, matchProb,
      price, Product.other]
  cases hf : σ .f <;> cases ht : σ .t <;> simp only [hf, ht, reduceCtorEq, if_true, if_false] <;>
    norm_num <;> split_ifs <;> nlinarith [sq_nonneg (q - 22289 / 30025)]

lemma seller_bound (σ : Ranking) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    sellerProfit hH hL rr (1 / 2) σ qs q ≤ sellerProfit hH hL rr (1 / 2) (fun _ => .T) qs 1 := by
  simp only [sellerProfit, demand, sumC, mass, typeDemand, promDemand, nonpromDemand, matchProb,
      price, Product.other]
  cases hf : σ .f <;> cases ht : σ .t <;> simp only [hf, ht, reduceCtorEq, if_true, if_false] <;>
    norm_num <;> split_ifs <;> nlinarith [sq_nonneg (q - qs), mul_nonneg hq0 (sub_nonneg.2 hq1)]

lemma ns_eq : IsNSEquilibrium hH hL rr (1 / 2) qs 1 (σopt hH hL rr) := by
  refine ⟨σopt_opt _ _ _, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · intro q hq
    rw [σ_at]
    exact plat_bound _ q hq.1 hq.2
  · intro q hq
    rw [σ_at]
    exact seller_bound _ q hq.1 hq.2

lemma s_eq : IsSEquilibrium hH hL rr (1 / 2) 1 1 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · intro q hq
    obtain ⟨hq0, hq1⟩ := hq
    simp only [platformProfit, demand, sumC, mass, typeDemand, promDemand, nonpromDemand,
      matchProb, price, Product.other, neutral]
    norm_num
    split_ifs <;> nlinarith
  · intro q hq
    obtain ⟨hq0, hq1⟩ := hq
    simp only [sellerProfit, demand, sumC, mass, typeDemand, promDemand, nonpromDemand,
      matchProb, price, Product.other, neutral]
    norm_num
    split_ifs <;> nlinarith

end SNP5Disproof



open SNP5Disproof in
theorem solution : ¬ (∀ (ρH ρL r : ℝ), 0 < ρL → ρL < ρH → ρH < 1 → 0 ≤ r → r < 1 →
    (ρL / ρH < r →
      (∃ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ) ∧
      ∀ (pF pT : ℝ) (σ : ℝ → ℝ → Ranking), IsNSEquilibrium ρH ρL r (1 / 2) pF pT σ →
        σ pF pT = neutral ∧ pF = 1 ∧ pT = 1) ∧
    (r = ρL / ρH →
      ∃ σ : ℝ → ℝ → Ranking, IsNSEquilibrium ρH ρL r (1 / 2) 1 1 σ ∧ σ 1 1 = neutral)) := by
  intro h1
  have h := ((h1 hH hL rr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
    (by norm_num)).2 qs 1 (σopt hH hL rr) ns_eq
  have := h.2.1
  norm_num at this
