-- Prove2me | solution 1 for SeasonalPricing.Announced.threshold_nash_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T02:19:40.045251+00:00
-- url     : https://prove2.me/submissions/90b7a6c0-cd43-406e-bee7-d5809ec8627a

import Mathlib
import Definitions.Def_SeasonalPricing_Announced_availability

set_option autoImplicit false

open MeasureTheory SeasonalPricing.Announced in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hF : Continuous (ProbabilityTheory.cdf μ))
    (lam α T : ℝ) (Q : ℕ) (p1 p2 w : ℝ)
    (hlam : 0 < lam) (hα : 0 ≤ α) (hT : 0 < T) (hQ : 1 ≤ Q) (hp : p2 ≤ p1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hdeg : 0 < α ∨ w < 1)
    (h8 : w = availability μ lam α T Q p1 p2 w) :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ V : ℝ,
      buysNow α T p1 p2 (availability μ lam α T Q p1 p2 w) t V ↔
        psiA α T p1 p2 w t ≤ valuation α V t := by
  intro t ht0 htT V
  rw [← h8]
  have hEle : Real.exp (-(α * (T - t))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hEpos : 0 < Real.exp (-(α * (T - t))) := Real.exp_pos _
  have hD : 0 < 1 - w * Real.exp (-(α * (T - t))) := by
    rcases hdeg with h | h
    · have hlt : Real.exp (-(α * (T - t))) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      nlinarith
    · nlinarith
  have hvT : valuation α V T = valuation α V t * Real.exp (-(α * (T - t))) := by
    unfold valuation
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  unfold buysNow psiA
  rw [hvT, max_le_iff, div_le_iff₀ hD]
  set u := valuation α V t with hu
  set E := Real.exp (-(α * (T - t))) with hE
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    have hm : w * (u * E - p2) ≤ w * max (u * E - p2) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hw0
    nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    rcases le_total (u * E - p2) 0 with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      nlinarith
