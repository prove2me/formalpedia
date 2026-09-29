-- Prove2me | solution 1 for WorkbookCorrected.base_15599
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:13:49.262013+00:00
-- url     : https://prove2.me/submissions/cb055171-f29b-4e23-a85a-33753218ec51

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (hab : a * b ≥ 3 / 2) : 3 * (2 * b + a - 3) * (2 * a + b - 3) ≥ (a - b) ^ 2 + 21 / 20  := by
  have hw0 : 0 ≤ (a*b - 3/2) := by linarith only [hab]
  have hsum : 0 ≤ (729/20 : ℝ) * (1) * (-10*a/27 - 10*b/27 + 1)^2 + (7 : ℝ) * ((a*b - 3/2)) * (1)^2 := by positivity
  have hid : ( 3 * (2 * b + a - 3) * (2 * a + b - 3) ) - ( (a - b) ^ 2 + 21 / 20  ) = (729/20 : ℝ) * (1) * (-10*a/27 - 10*b/27 + 1)^2 + (7 : ℝ) * ((a*b - 3/2)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (hab : a * b ≥ 3 / 2), 3 * (2 * b + a - 3) * (2 * a + b - 3) ≥ (a - b) ^ 2 + 21 / 20) := @solution
#print axioms solution
