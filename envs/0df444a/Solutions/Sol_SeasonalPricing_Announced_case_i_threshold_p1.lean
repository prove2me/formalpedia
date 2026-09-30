-- Prove2me | solution 1 for SeasonalPricing.Announced.case_i_threshold_p1
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:01:47.713263+00:00
-- url     : https://prove2.me/submissions/bacf9c12-6ccd-4547-9f2c-0383bc17ba76

import Mathlib
import Definitions.Def_SeasonalPricing_Announced_purchaseRule

open SeasonalPricing.Announced

theorem solution (α T p1 p2 w t : ℝ) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (htT : t < T)
    (hp1 : 0 < p1) (hp : p2 ≤ p1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hcase : Real.exp (-(α * (T - t))) ≤ p2 / p1) (V : ℝ) :
    buysNow α T p1 p2 w t V ↔ p1 ≤ valuation α V t := by
  have hTt : 0 < T - t := sub_pos.mpr htT
  have harg : 0 ≤ α * (T - t) := mul_nonneg hα hTt.le
  have hexp_le_one : Real.exp (-(α * (T - t))) ≤ 1 := by
    have := Real.exp_le_exp.mpr (show -(α * (T - t)) ≤ 0 by linarith)
    simpa using this
  have h1me : 0 ≤ 1 - Real.exp (-(α * (T - t))) := by linarith
  have hp2_ge : p1 * Real.exp (-(α * (T - t))) ≤ p2 := by
    have h := (le_div_iff₀ hp1).mp hcase
    nlinarith [h]
  have hexp_eq : valuation α V t * Real.exp (-(α * (T - t))) = valuation α V T := by
    simp only [valuation]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  have hsecond (hp1le : p1 ≤ valuation α V t) :
      w * max (valuation α V T - p2) 0 ≤ valuation α V t - p1 := by
    have hmain : valuation α V T - p2 ≤ valuation α V t - p1 := by
      have h1 : p1 - p2 ≤ p1 * (1 - Real.exp (-(α * (T - t)))) := by
        nlinarith [hp2_ge]
      have h2 : p1 * (1 - Real.exp (-(α * (T - t)))) ≤
          valuation α V t * (1 - Real.exp (-(α * (T - t)))) :=
        mul_le_mul_of_nonneg_right hp1le h1me
      have h3 : valuation α V t * (1 - Real.exp (-(α * (T - t)))) =
          valuation α V t - valuation α V T := by
        rw [mul_sub, mul_one, hexp_eq]
      linarith
    rcases le_total (valuation α V T - p2) 0 with h | h
    · rw [max_eq_right h]
      nlinarith
    · rw [max_eq_left h]
      have := mul_le_mul_of_nonneg_right hw1 h
      linarith
  constructor
  · intro h
    exact sub_nonneg.mp h.1
  · intro hp1le
    exact ⟨sub_nonneg.mpr hp1le, hsecond hp1le⟩
