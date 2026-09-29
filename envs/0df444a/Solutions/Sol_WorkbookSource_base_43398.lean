-- Prove2me | solution 1 for WorkbookSource.base_43398
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:29.656031+00:00
-- url     : https://prove2.me/submissions/503eded3-8200-4385-ad14-16f4b67dc8ae

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a^2 + b^2 + c^2 - 1)^2 ≥ 2 * (a^3 * b + b^3 * c + c^3 * a - 1)  := by
  have h0 : 0 ≤ (3 : ℝ) * (1) * (-a^2/3 - b^2/3 - c^2/3 + 1)^2 := by positivity
  have h1 : 0 ≤ (2 : ℝ) * (1) * (a^2/2 - a*b/2 - a*c/2 - b^2/2 + b*c)^2 := by positivity
  have h2 : 0 ≤ (3/2 : ℝ) * (1) * (a^2/3 - a*b + a*c + b^2/3 - 2*c^2/3)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a^2 + b^2 + c^2 - 1)^2 ≥ 2 * (a^3 * b + b^3 * c + c^3 * a - 1)) := @solution
#print axioms solution
