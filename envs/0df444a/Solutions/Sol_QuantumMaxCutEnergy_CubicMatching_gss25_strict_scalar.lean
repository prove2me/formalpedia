-- Prove2me | solution 1 for QuantumMaxCutEnergy.CubicMatching.gss25_strict_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:30:38.55505+00:00
-- url     : https://prove2.me/submissions/b019a400-0f12-438d-8006-0a2ad5f73bff

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace QuantumMaxCutEnergy.CubicMatching

theorem lp24_strict_scalar (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (0.5955 : ℝ) * ((1 + 3 * s) / 2) ≤
      0.672 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
        (1 - 0.672) * (1 / 2 + (3 / 2) * (4 / 5) * max ((3 * s - 1) / 2) 0) := by
  by_cases hcut : (3 * s - 1) / 2 ≤ 0
  · rw [max_eq_right hcut]
    have hst : s ≤ 1 / 3 := by linarith
    have hc : 0 ≤ (s - 1 / 3) ^ 2 * (s + 2 / 3) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith only [hst, hc]
  · rw [max_eq_left (le_of_lt (lt_of_not_ge hcut))]
    have hc : 0 ≤ (s - 0.4542) ^ 2 * (s + 2 * 0.4542) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith only [hc, hs1]

theorem gss25_strict_scalar (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (0.6031 : ℝ) * ((1 + 3 * s) / 2) ≤
      0.724 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
        (1 - 0.724) * (1 / 2 + (3 / 2) * (14 / 15) * max ((3 * s - 1) / 2) 0) := by
  by_cases hcut : (3 * s - 1) / 2 ≤ 0
  · rw [max_eq_right hcut]
    have hst : s ≤ 1 / 3 := by linarith
    have hc : 0 ≤ (s - 1 / 3) ^ 2 * (s + 2 / 3) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith only [hst, hc]
  · rw [max_eq_left (le_of_lt (lt_of_not_ge hcut))]
    have hc : 0 ≤ (s - 0.4392) ^ 2 * (s + 2 * 0.4392) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith only [hc, hs1]

#print axioms lp24_strict_scalar
#print axioms gss25_strict_scalar

end QuantumMaxCutEnergy.CubicMatching

theorem solution (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (0.6031 : ℝ) * ((1 + 3 * s) / 2) ≤
      0.724 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
        (1 - 0.724) * (1 / 2 + (3 / 2) * (14 / 15) * max ((3 * s - 1) / 2) 0) := by
  exact QuantumMaxCutEnergy.CubicMatching.gss25_strict_scalar s hs hs1
#print axioms solution
