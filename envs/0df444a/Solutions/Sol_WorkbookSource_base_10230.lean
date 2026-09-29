-- Prove2me | solution 1 for WorkbookSource.base_10230
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:19.764439+00:00
-- url     : https://prove2.me/submissions/aa8442bb-e3cf-408c-a891-09ec20989b9b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (M c k : ℝ) : M * (M + 2 * k * c ^ 2) * (1 - k ^ 2) ≤ (M + (k - k ^ 2) * c ^ 2) ^ 2  := by
  have hsum : 0 ≤ (1 : ℝ) * (-M*k - c^2*k^2 + c^2*k)^2 := by positivity
  have hid : ( (M + (k - k ^ 2) * c ^ 2) ^ 2  ) - ( M * (M + 2 * k * c ^ 2) * (1 - k ^ 2) ) = (1 : ℝ) * (-M*k - c^2*k^2 + c^2*k)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (M c k : ℝ), M * (M + 2 * k * c ^ 2) * (1 - k ^ 2) ≤ (M + (k - k ^ 2) * c ^ 2) ^ 2) := @solution
#print axioms solution
