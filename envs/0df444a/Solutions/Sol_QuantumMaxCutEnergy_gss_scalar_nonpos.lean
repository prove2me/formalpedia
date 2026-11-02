-- Prove2me | solution 1 for QuantumMaxCutEnergy.gss_scalar_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T04:51:52.2992+00:00
-- url     : https://prove2.me/submissions/4b79350c-9a3a-4a83-9c87-ab60c93b3a0b

import Mathlib

/-- **GSS25's mixing scalar on the negative half of the admissible range.**

For `s ∈ [-1/3, 0]` the matching (positive-excess) term vanishes and the product term alone
carries the inequality, with the platform's proved positive-half scalar (`gss25_strict_scalar`,
`s ∈ [0,1]`) completing the coverage of the full range `[-1/3, 1]`. -/
theorem QuantumMaxCutEnergy.gss_scalar_nonpos (s : ℝ) (h1 : -1 / 3 ≤ s) (h2 : s ≤ 0) :
    (0.6031 : ℝ) * ((1 + 3 * s) / 2) ≤
      0.724 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
        (1 - 0.724) * (1 / 2 + (3 / 2) * (14 / 15) * max ((3 * s - 1) / 2) 0) := by
  have hm : (0 : ℝ) ≤ max ((3 * s - 1) / 2) 0 := le_max_right _ _
  have hs2 : s ^ 2 ≤ 1 / 9 := by nlinarith
  have hs3 : s ^ 3 ≥ -(1 / 27) := by
    have h : s ^ 3 = s * s ^ 2 := by ring
    rw [h]
    nlinarith
  nlinarith

theorem solution (s : ℝ) (h1 : -1 / 3 ≤ s) (h2 : s ≤ 0) :
    (0.6031 : ℝ) * ((1 + 3 * s) / 2) ≤
      0.724 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
        (1 - 0.724) * (1 / 2 + (3 / 2) * (14 / 15) * max ((3 * s - 1) / 2) 0) :=
  QuantumMaxCutEnergy.gss_scalar_nonpos s h1 h2

#print axioms solution
