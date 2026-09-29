-- Prove2me | solution 1 for WorkbookSource.base_18542
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:47:38.025916+00:00
-- url     : https://prove2.me/submissions/c90fc34e-af8f-4ad1-bf5c-1eb521af86bc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h₁ : a ≥ b + 1) (h₂ : b ≥ c + 4) : a^2 + b^2 + c^2 ≥ 14  := by
  have hw0 : 0 ≤ (a - b - 1) := by linarith only [h₁]
  have hw1 : 0 ≤ (b - c - 4) := by linarith only [h₂]
  have hsum : 0 ≤ (6 : ℝ) * (1) * (a/3 - 2*b/3 + c/3 + 1)^2 + (1/3 : ℝ) * (1) * (a + b + c)^2 + (6 : ℝ) * ((b - c - 4)) * (1)^2 + (4 : ℝ) * ((a - b - 1)) * (1)^2 + (2 : ℝ) * ((a - b - 1) * (b - c - 4)) * (1)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 ) - ( 14  ) = (6 : ℝ) * (1) * (a/3 - 2*b/3 + c/3 + 1)^2 + (1/3 : ℝ) * (1) * (a + b + c)^2 + (6 : ℝ) * ((b - c - 4)) * (1)^2 + (4 : ℝ) * ((a - b - 1)) * (1)^2 + (2 : ℝ) * ((a - b - 1) * (b - c - 4)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h₁ : a ≥ b + 1) (h₂ : b ≥ c + 4), a^2 + b^2 + c^2 ≥ 14) := @solution
#print axioms solution
