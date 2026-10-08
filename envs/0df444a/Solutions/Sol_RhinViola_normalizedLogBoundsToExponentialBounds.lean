-- Prove2me | solution 1 for RhinViola.normalizedLogBoundsToExponentialBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T14:21:38.46699+00:00
-- url     : https://prove2.me/submissions/88bb4532-c1ff-4a26-9f2f-ffc16853aca9

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem solution
    (σ δ f : ℝ) (n : ℕ)
    (hn : 0 < n) (hf : f ≠ 0)
    (hlo : -(σ + δ) ≤ Real.log |f| / (n : ℝ))
    (hhi : Real.log |f| / (n : ℝ) ≤ -(σ - δ)) :
    Real.exp (-((σ + δ) * (n : ℝ))) ≤ |f| ∧
      |f| ≤ Real.exp (-((σ - δ) * (n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have habs : 0 < |f| :=
    abs_pos.mpr hf
  have hlo' :
      -(σ + δ) * (n : ℝ) ≤ Real.log |f| :=
    (le_div_iff₀ hnR).mp hlo
  have hhi' :
      Real.log |f| ≤ -(σ - δ) * (n : ℝ) :=
    (div_le_iff₀ hnR).mp hhi
  constructor
  · have h := Real.exp_le_exp.mpr hlo'
    rw [Real.exp_log habs] at h
    simpa only [neg_mul] using h
  · have h := Real.exp_le_exp.mpr hhi'
    rw [Real.exp_log habs] at h
    simpa only [neg_mul] using h
