-- Prove2me | solution 1 for SeasonalPricing.Announced.case_ii_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T13:33:46.605378+00:00
-- url     : https://prove2.me/submissions/a332ff46-ac8e-42cb-bf26-0f1fbe0e7732

import Mathlib
import Definitions.Def_SeasonalPricing_Announced_purchaseRule

set_option autoImplicit false

open SeasonalPricing.Announced in
theorem solution (α T p1 p2 w t : ℝ) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (htT : t < T)
    (hp1 : 0 < p1) (hp : p2 ≤ p1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hwδ : w * Real.exp (-(α * (T - t))) < 1)
    (hcase : p2 / p1 < Real.exp (-(α * (T - t)))) :
    p1 ≤ (p1 - w * p2) / (1 - w * Real.exp (-(α * (T - t)))) ∧
      ∀ V : ℝ, buysNow α T p1 p2 w t V ↔
        (p1 - w * p2) / (1 - w * Real.exp (-(α * (T - t)))) ≤ valuation α V t := by
  have hEpos : 0 < Real.exp (-(α * (T - t))) := Real.exp_pos _
  have hD : 0 < 1 - w * Real.exp (-(α * (T - t))) := by linarith
  have hc : p2 < p1 * Real.exp (-(α * (T - t))) := by
    rwa [div_lt_iff₀ hp1, mul_comm] at hcase
  have hthr : p1 ≤ (p1 - w * p2) / (1 - w * Real.exp (-(α * (T - t)))) := by
    rw [le_div_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_left hc.le hw0]
  refine ⟨hthr, fun V => ?_⟩
  have hvT : valuation α V T = valuation α V t * Real.exp (-(α * (T - t))) := by
    unfold valuation
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  unfold buysNow
  rw [hvT]
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hD]
    set u := valuation α V t with hu
    set E := Real.exp (-(α * (T - t))) with hE
    rcases le_total (u * E - p2) 0 with h | h
    · exfalso
      nlinarith [mul_le_mul_of_nonneg_right (show p1 ≤ u by linarith) hEpos.le]
    · rw [max_eq_left h] at h2
      nlinarith
  · intro h
    have hu1 : p1 ≤ valuation α V t := le_trans hthr h
    rw [div_le_iff₀ hD] at h
    set u := valuation α V t with hu
    set E := Real.exp (-(α * (T - t))) with hE
    refine ⟨by linarith, ?_⟩
    rcases le_total (u * E - p2) 0 with h' | h'
    · rw [max_eq_right h']
      linarith
    · rw [max_eq_left h']
      nlinarith
