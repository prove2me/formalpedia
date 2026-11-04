-- Prove2me | solution 1 for PerishBaseStock.Population.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:53:36.479545+00:00
-- url     : https://prove2.me/submissions/c23085f5-449e-499c-8794-7c1b23993c09

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand
import Theorems.Thm_PerishBaseStock_Population_eq_23
import Theorems.Thm_PerishBaseStock_Population_step1_claim
import Theorems.Thm_PerishBaseStock_Population_eq_EC_8

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace Pop2R

theorem exp_neg_le (y : ℝ) (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 := by
  have h1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
  have h2 : Real.exp (-y) * (1 + y) ≤ 1 := by
    have := Real.add_one_le_exp y
    calc Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y := by
          apply mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- `E[e^{-l D̂}] ≤ 1 - l μ + l² E[D̂²]`. -/
theorem lap_le (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ)
    (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) {l : ℝ} (hl : 0 ≤ l) :
    ∫ x : ℝ≥0, Real.exp (-(l * (x : ℝ))) ∂ρ ≤
      1 - l * ∫ x : ℝ≥0, (x : ℝ) ∂ρ + l ^ 2 * ∫ x : ℝ≥0, (x : ℝ) ^ 2 ∂ρ := by
  have hint : Integrable (fun x : ℝ≥0 => Real.exp (-(l * (x : ℝ)))) ρ := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [NNReal.coe_nonneg x])
  have hR : Integrable (fun x : ℝ≥0 => 1 - l * (x : ℝ) + l ^ 2 * (x : ℝ) ^ 2) ρ :=
    ((integrable_const _).sub (h1.const_mul _)).add (h2.const_mul _)
  calc ∫ x : ℝ≥0, Real.exp (-(l * (x : ℝ))) ∂ρ ≤
        ∫ x : ℝ≥0, (1 - l * (x : ℝ) + l ^ 2 * (x : ℝ) ^ 2) ∂ρ :=
        integral_mono hint hR fun x => by
          have := exp_neg_le (l * x) (mul_nonneg hl (NNReal.coe_nonneg x))
          nlinarith
    _ = _ := by
        have hA : Integrable (fun x : ℝ≥0 => 1 - l * (x : ℝ)) ρ :=
          (integrable_const _).sub (h1.const_mul _)
        have hB : Integrable (fun x : ℝ≥0 => l * (x : ℝ)) ρ := h1.const_mul _
        have hC : Integrable (fun x : ℝ≥0 => l ^ 2 * (x : ℝ) ^ 2) ρ := h2.const_mul _
        rw [integral_add hA hC, integral_sub (integrable_const _) hB, integral_const_mul,
          integral_const_mul]
        simp

end Pop2R

open Pop2R PerishBaseStock.Population in
theorem solution (c : PerishBaseStock.Lifetime.Params) (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ K₂ : ℝ, 0 < K₂ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ S : ℝ≥0, PerishBaseStock.Lifetime.IsHeuristicLevel (P n) c S →
        baseStockCost (P n) c S ≤
          OPT (P n) c + ENNReal.ofReal (K₁ * Real.exp (-(K₂ * (n : ℝ)))) := by
  obtain ⟨ν, hν, h8⟩ := eq_EC_8 X
  obtain ⟨n1, hn1, hS1⟩ := step1_claim c Dh X hμ P hP (3 / 2) (by norm_num)
  set μ := customerMean Dh with hμdef
  have h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) Dh.law := Dh.memLp_two.integrable one_le_two
  have h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) Dh.law := Dh.memLp_two.integrable_sq
  set M2 := ∫ x : ℝ≥0, (x : ℝ) ^ 2 ∂Dh.law with hM2
  have hM2 : 0 ≤ M2 := integral_nonneg fun _ => sq_nonneg _
  -- choice of δ
  set δ := min (ν / 2) (1 / 8) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδν : δ < ν := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ8 : δ ≤ 1 / 8 := min_le_right _ _
  set cδ := δ ^ 2 / (8 * (1 + δ) ^ 2 * ν ^ 2) with hcδ
  have hcδ0 : 0 < cδ := by positivity
  -- choice of λ
  set lam := min (μ / (16 * (M2 + 1))) (cδ / (2 * μ)) with hlamdef
  have hlam0 : 0 < lam := lt_min (by positivity) (by positivity)
  have hlamM : lam * M2 ≤ μ / 16 := by
    have : lam ≤ μ / (16 * (M2 + 1)) := min_le_left _ _
    have h' : lam * (M2 + 1) ≤ μ / 16 := by
      rw [le_div_iff₀ (by positivity)] at this
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    nlinarith
  have hlamc : lam * μ ≤ cδ / 2 := by
    have : lam ≤ cδ / (2 * μ) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  set γ := min (lam * μ / 12) (cδ / 2) with hγdef
  have hγ0 : 0 < γ := lt_min (by positivity) (by positivity)
  -- Laplace transform of one customer
  set φ := ∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂Dh.law with hφ
  have hφ0 : 0 ≤ φ := integral_nonneg fun _ => (Real.exp_pos _).le
  set a := lam * μ - lam ^ 2 * M2 with ha
  have ha1 : 15 / 16 * (lam * μ) ≤ a := by
    have : lam ^ 2 * M2 ≤ lam * (μ / 16) := by
      rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_left hlamM hlam0.le
    rw [ha]; nlinarith
  have hφa : φ ≤ Real.exp (-a) := by
    have hl : φ ≤ 1 - lam * μ + lam ^ 2 * M2 := lap_le Dh.law h1 h2 hlam0.le
    have := Real.add_one_le_exp (-a)
    rw [ha] at this ⊢; linarith
  -- constants
  set m : ℕ := c.m with hmdef
  set κ : ℝ := ((m : ℝ) - 1) * c.θ / (lam * (m : ℝ) * Real.exp 1) with hκ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast c.one_le_m
  have hκ0 : 0 ≤ κ := by
    have := c.θ_nonneg
    apply div_nonneg (mul_nonneg (by linarith) this)
    positivity
  refine ⟨κ * 2 ^ m + 1, by positivity, γ, hγ0, max n1 ⌈2 * (1 + δ) / δ⌉₊, ?_⟩
  intro n hn S hS
  have hn1' : n1 ≤ n := le_of_max_le_left hn
  have hn2 : 2 * (1 + δ) / δ ≤ (n : ℝ) := (Nat.ceil_le).1 (le_of_max_le_right hn)
  have hn1pos : 1 ≤ n := le_trans hn1 hn1'
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h23 := eq_23 c Dh X hμ P hP n hn1pos lam hlam0 S hS
  refine h23.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  -- the real inequality
  set Y := ∫ ω, Real.exp (-(lam * (compoundDemand n ω : ℝ))) ∂popSampleLaw Dh X with hY
  set SN : ℝ := (newsvendorLevel (P n) c : ℝ) with hSN
  set Z := Real.exp ((1 / (m : ℝ)) * lam * SN) * Y with hZ
  have hY0 : 0 ≤ Y := integral_nonneg fun _ => (Real.exp_pos _).le
  have hZ0 : 0 ≤ Z := mul_nonneg (Real.exp_pos _).le hY0
  have hexpo : 0 < 2 * γ := by linarith
  change κ * Z ^ m ≤ (κ * 2 ^ m + 1) * Real.exp (-(γ * n))
  by_cases hm : m = 1
  · have : κ = 0 := by rw [hκ, hm]; simp
    rw [this]; simp only [zero_mul, zero_add, one_mul]; exact (Real.exp_pos _).le
  have hm2 : (2 : ℝ) ≤ m := by
    have : 2 ≤ m := by have := c.one_le_m; omega
    exact_mod_cast this
  -- bound on Y
  have hY8 := h8 Dh hμ δ hδ0 hδν n hn2 lam hlam0
  rw [← hY, ← hφ] at hY8
  have hφpow : φ ^ ((n : ℝ) / (1 + δ)) ≤ Real.exp (-(5 / 6 * (lam * μ) * n)) := by
    calc φ ^ ((n : ℝ) / (1 + δ)) ≤ Real.exp (-a) ^ ((n : ℝ) / (1 + δ)) :=
          Real.rpow_le_rpow hφ0 hφa (by positivity)
      _ = Real.exp (-a * ((n : ℝ) / (1 + δ))) := by rw [← Real.exp_mul]
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          have hq : 8 / 9 * (n : ℝ) ≤ (n : ℝ) / (1 + δ) := by
            rw [le_div_iff₀ (by linarith)]; nlinarith
          have ha0 : 0 ≤ a := le_trans (by positivity) ha1
          have : a * (8 / 9 * (n : ℝ)) ≤ a * ((n : ℝ) / (1 + δ)) :=
            mul_le_mul_of_nonneg_left hq ha0
          nlinarith
  have hYb : Y ≤ Real.exp (-(cδ * n)) + Real.exp (-(5 / 6 * (lam * μ) * n)) := by
    have e : Real.exp (-(δ ^ 2 * (n : ℝ) / (8 * (1 + δ) ^ 2 * ν ^ 2))) = Real.exp (-(cδ * n)) := by
      rw [hcδ]; congr 1; ring
    rw [e] at hY8; linarith
  -- bound on the newsvendor factor
  have hSb : SN ≤ 3 / 2 * μ * n := hS1 n hn1'
  have hSN0 : 0 ≤ SN := NNReal.coe_nonneg _
  have hE1 : Real.exp ((1 / (m : ℝ)) * lam * SN) ≤ Real.exp (3 / 4 * (lam * μ) * n) := by
    apply Real.exp_le_exp.2
    have hinv : 1 / (m : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hinv0 : 0 ≤ 1 / (m : ℝ) := by positivity
    calc (1 / (m : ℝ)) * lam * SN ≤ (1 / 2) * lam * SN := by
          apply mul_le_mul_of_nonneg_right _ hSN0
          exact mul_le_mul_of_nonneg_right hinv hlam0.le
      _ ≤ (1 / 2) * lam * (3 / 2 * μ * n) :=
          mul_le_mul_of_nonneg_left hSb (by positivity)
      _ = _ := by ring
  have hZb : Z ≤ 2 * Real.exp (-(γ * n)) := by
    calc Z ≤ Real.exp (3 / 4 * (lam * μ) * n) *
          (Real.exp (-(cδ * n)) + Real.exp (-(5 / 6 * (lam * μ) * n))) :=
          mul_le_mul hE1 hYb hY0 (Real.exp_pos _).le
      _ = Real.exp (3 / 4 * (lam * μ) * n + -(cδ * n)) +
          Real.exp (3 / 4 * (lam * μ) * n + -(5 / 6 * (lam * μ) * n)) := by
          rw [mul_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (-(γ * n)) + Real.exp (-(γ * n)) := by
          apply add_le_add
          · apply Real.exp_le_exp.2
            have : γ ≤ cδ / 2 := min_le_right _ _
            have : γ * n ≤ cδ / 2 * n := mul_le_mul_of_nonneg_right this hnR
            have : lam * μ * n ≤ cδ / 2 * n := mul_le_mul_of_nonneg_right hlamc hnR
            have := mul_nonneg hcδ0.le hnR
            linarith
          · apply Real.exp_le_exp.2
            have : γ ≤ lam * μ / 12 := min_le_left _ _
            have : γ * n ≤ lam * μ / 12 * n := mul_le_mul_of_nonneg_right this hnR
            linarith
      _ = _ := by ring
  have hZm : Z ^ m ≤ 2 ^ m * Real.exp (-(γ * n)) := by
    calc Z ^ m ≤ (2 * Real.exp (-(γ * n))) ^ m := pow_le_pow_left₀ hZ0 hZb m
      _ = 2 ^ m * Real.exp (-(γ * n)) ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * Real.exp (-(γ * n)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_of_le_one (Real.exp_pos _).le
          · exact Real.exp_le_one_iff.2 (by have := mul_nonneg hγ0.le hnR; linarith)
          · have := c.one_le_m; omega
  calc κ * Z ^ m ≤ κ * (2 ^ m * Real.exp (-(γ * n))) := mul_le_mul_of_nonneg_left hZm hκ0
    _ ≤ (κ * 2 ^ m + 1) * Real.exp (-(γ * n)) := by
        rw [add_mul, one_mul, ← mul_assoc]; linarith [Real.exp_pos (-(γ * n))]
