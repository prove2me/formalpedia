-- Prove2me | solution 1 for RhinViola.normalizedLogCoefficientBoundToExponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T14:18:44.24728+00:00
-- url     : https://prove2.me/submissions/b48b9c81-d43c-466d-b857-73c18ff7b1a6

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem solution
    (ρ δ : ℝ) (b : ℤ) (n : ℕ)
    (hn : 0 < n)
    (hlog : Real.log |(b : ℝ)| / (n : ℝ) ≤ ρ + δ) :
    |(b : ℝ)| ≤ Real.exp ((ρ + δ) * (n : ℝ)) := by
  by_cases hb : b = 0
  · subst b
    norm_num
    positivity
  · have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    have hbR : (b : ℝ) ≠ 0 := by
      exact_mod_cast hb
    have habs : 0 < |(b : ℝ)| :=
      abs_pos.mpr hbR
    have hlog' :
        Real.log |(b : ℝ)| ≤ (ρ + δ) * (n : ℝ) :=
      (div_le_iff₀ hnR).mp hlog
    have h := Real.exp_le_exp.mpr hlog'
    rw [Real.exp_log habs] at h
    exact h
