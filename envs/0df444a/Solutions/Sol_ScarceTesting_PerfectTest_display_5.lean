-- Prove2me | solution 1 for ScarceTesting.PerfectTest.display_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:57:39.864644+00:00
-- url     : https://prove2.me/submissions/6c29388f-24a8-466f-ac4e-9d31bc2575cf

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

set_option autoImplicit false
open MeasureTheory Set ScarceTesting.PerfectTest

theorem solution (c φ σ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1) :
    tL c φ σ ≤ c ∧ c ≤ tH c φ σ := by
  have h1c : 0 < 1 - c := by linarith
  have h1φ : 0 < 1 - φ := by linarith
  constructor
  · have hd : 0 < c * φ + (1 - c) * σ := by positivity
    unfold tL
    rw [div_le_iff₀ hd]
    nlinarith [mul_nonneg (mul_nonneg hc0.le h1c.le) (sub_nonneg.2 hφσ)]
  · have hd : 0 < c * (1 - φ) + (1 - c) * (1 - σ) := by
      have : 0 ≤ (1 - c) * (1 - σ) := mul_nonneg h1c.le (by linarith)
      have : 0 < c * (1 - φ) := by positivity
      linarith
    unfold tH
    rw [le_div_iff₀ hd]
    nlinarith [mul_nonneg (mul_nonneg hc0.le h1c.le) (sub_nonneg.2 hφσ)]
