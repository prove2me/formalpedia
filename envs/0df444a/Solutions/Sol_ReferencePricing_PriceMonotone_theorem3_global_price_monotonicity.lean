-- Prove2me | solution 1 for ReferencePricing.PriceMonotone.theorem3_global_price_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:19:25.496082+00:00
-- url     : https://prove2.me/submissions/0052a1f9-7289-483c-bc82-38294452cd73

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_ReferencePricing_PriceMonotone_LemmaThreeCondition
import Theorems.Thm_ReferencePricing_PriceMonotone_theorem2_global_stability
import Theorems.Thm_ReferencePricing_PriceMonotone_lemma3a_short_memory
import Theorems.Thm_ReferencePricing_PriceMonotone_lemma3b_convex_demand
open RobustBooking.Shared

open Filter Topology

/-- Condition (c) of Lemma 3 is incompatible with Assumption 1 on `P = [0, p̄]`. -/
theorem refprice3_not_condC (pbar : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hA1 : Assumption1 pbar d R)
    (hc : ReferencePricing.PriceMonotone.IsStronglyConcaveOn (profit d R)
      (Set.Ioo (0 : ℝ) pbar ×ˢ Set.Ioo (0 : ℝ) pbar)) : False := by
  obtain ⟨-, a, b, ha, hb, hconc⟩ := hc
  obtain ⟨M, hM⟩ := hA1.bounded
  have hM0 : 0 ≤ M := le_trans (hA1.nonneg 0 ⟨le_rfl, hpbar.le⟩ 0 ⟨le_rfl, hpbar.le⟩)
    (hM 0 ⟨le_rfl, hpbar.le⟩ 0 ⟨le_rfl, hpbar.le⟩)
  -- choose p small
  set p : ℝ := min (pbar / 2) (b * pbar ^ 2 / (32 * (M + 1))) with hpdef
  have hp0 : 0 < p := lt_min (by linarith) (by positivity)
  have hp1 : p < pbar := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hp2 : p ≤ b * pbar ^ 2 / (32 * (M + 1)) := min_le_right _ _
  have m1 : ((p, pbar / 4) : ℝ × ℝ) ∈ Set.Ioo (0 : ℝ) pbar ×ˢ Set.Ioo (0 : ℝ) pbar :=
    ⟨⟨hp0, hp1⟩, ⟨by positivity, by linarith⟩⟩
  have m2 : ((p, 3 * pbar / 4) : ℝ × ℝ) ∈ Set.Ioo (0 : ℝ) pbar ×ˢ Set.Ioo (0 : ℝ) pbar :=
    ⟨⟨hp0, hp1⟩, ⟨by positivity, by linarith⟩⟩
  have key := hconc.2 m1 m2 (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (by norm_num)
  have hmid : (1/2 : ℝ) • ((p, pbar / 4) : ℝ × ℝ) + (1/2 : ℝ) • (p, 3 * pbar / 4) = (p, pbar / 2) := by
    ext <;> simp <;> ring
  rw [hmid] at key
  simp only [smul_eq_mul] at key
  have hPi : ∀ r, profit d R p r = p * demand d R p r := fun r => rfl
  rw [hPi, hPi, hPi] at key
  have hpI : p ∈ Set.Icc (0 : ℝ) pbar := ⟨hp0.le, hp1.le⟩
  have e1 := hA1.nonneg p hpI (pbar / 4) ⟨by positivity, by linarith⟩
  have e2 := hA1.nonneg p hpI (3 * pbar / 4) ⟨by positivity, by linarith⟩
  have e3 := hM p hpI (pbar / 2) ⟨by positivity, by linarith⟩
  -- key: p*Dmid + a p^2 + b (pbar/2)^2 ≥ 1/2 (p D1 + a p^2 + b r1^2) + 1/2 (...)
  have h1 : b * (pbar / 4) ^ 2 ≤ p * M := by
    have : p * demand d R p (pbar / 4) ≥ 0 := mul_nonneg hp0.le e1
    have : p * demand d R p (3 * pbar / 4) ≥ 0 := mul_nonneg hp0.le e2
    have : p * demand d R p (pbar / 2) ≤ p * M := mul_le_mul_of_nonneg_left e3 hp0.le
    nlinarith
  have h2 : p * M < b * (pbar / 4) ^ 2 := by
    have : p * M ≤ b * pbar ^ 2 / (32 * (M + 1)) * M := mul_le_mul_of_nonneg_right hp2 hM0
    have h3 : b * pbar ^ 2 / (32 * (M + 1)) * M < b * (pbar / 4) ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      have : 0 < b * pbar ^ 2 := by positivity
      nlinarith
    linarith
  linarith

theorem solution
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d)
    (hL3 : ReferencePricing.PriceMonotone.LemmaThreeCondition pbar α d R) :
    ∃ p : ℝ, IsSteadyState (profit d R) α β pbar p ∧
      (∀ q : ℝ, IsSteadyState (profit d R) α β pbar q → q = p) ∧
      deriv (baseProfit d) p / (1 - β) = p * refSlope R p / (1 - α * β) ∧
      (∀ q ∈ Set.Icc (0 : ℝ) pbar,
        deriv (baseProfit d) q / (1 - β) = q * refSlope R q / (1 - α * β) → q = p) ∧
      ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
        (Monotone (pricePath (profit d R) α β pbar r₀) ∨
          Antitone (pricePath (profit d R) α β pbar r₀)) ∧
        Tendsto (pricePath (profit d R) α β pbar r₀) atTop (𝓝 p) := by
  -- the price policy is monotone on P
  have hmono : MonotoneOn (optPrice (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by
    rcases hL3 with h | h | ⟨h, -⟩
    · exact ReferencePricing.PriceMonotone.lemma3a_short_memory pbar α β d R hpbar hα₀ hα₁
        hβ₀ hβ₁ hA1 hA2 hA3 hd h
    · exact ReferencePricing.PriceMonotone.lemma3b_convex_demand pbar α β d R hpbar hα₀ hα₁
        hβ₀ hβ₁ hA1 hA2 hA3 hd h
    · exact (refprice3_not_condC pbar d R hpbar hA1 h).elim
  -- optPrice always lies in P
  have hopt : ∀ r, optPrice (profit d R) α β pbar r ∈ Set.Icc (0 : ℝ) pbar := by
    intro r
    unfold optPrice
    set S := {p | p ∈ Set.Icc (0 : ℝ) pbar ∧ ∀ p' ∈ Set.Icc (0 : ℝ) pbar,
      bellmanObj (profit d R) α β pbar p' r ≤ bellmanObj (profit d R) α β pbar p r}
    rcases S.eq_empty_or_nonempty with hS | hS
    · rw [hS, Real.sSup_empty]; exact ⟨le_rfl, hpbar.le⟩
    · have hbdd : BddAbove S := ⟨pbar, fun x hx => hx.1.2⟩
      obtain ⟨x, hx⟩ := hS
      exact ⟨le_trans hx.1.1 (le_csSup hbdd hx), csSup_le ⟨x, hx⟩ (fun y hy => hy.1.2)⟩
  -- the state path stays in P
  have hstate : ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar, ∀ t,
      statePath (profit d R) α β pbar r₀ t ∈ Set.Icc (0 : ℝ) pbar := by
    intro r₀ hr₀ t
    induction t with
    | zero => exact hr₀
    | succ t ih =>
      show optRef (profit d R) α β pbar (statePath (profit d R) α β pbar r₀ t) ∈ _
      unfold optRef
      have h1 := hopt (statePath (profit d R) α β pbar r₀ t)
      set x := statePath (profit d R) α β pbar r₀ t
      set y := optPrice (profit d R) α β pbar x
      constructor
      · have := mul_nonneg hα₀ ih.1
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α) h1.1
        linarith
      · nlinarith [ih.2, h1.2]
  obtain ⟨p, h1, h2, h3, h4, h5⟩ :=
    ReferencePricing.PriceMonotone.theorem2_global_stability pbar α β d R hpbar hα₀ hα₁ hβ₀ hβ₁
      hA1 hA2 hA3 hd
  refine ⟨p, h1, h2, h3, h4, fun r₀ hr₀ => ⟨?_, (h5 r₀ hr₀).1⟩⟩
  rcases (h5 r₀ hr₀).2.1 with hm | ha
  · left
    intro s t hst
    exact hmono (hstate r₀ hr₀ s) (hstate r₀ hr₀ t) (hm hst)
  · right
    intro s t hst
    exact hmono (hstate r₀ hr₀ t) (hstate r₀ hr₀ s) (ha hst)
