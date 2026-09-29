-- Prove2me | solution 1 for WorkbookSource.plus_45827
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:12:20.415111+00:00
-- url     : https://prove2.me/submissions/e5a4d589-8263-4291-8a05-826a2de2fae8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a : ℝ) : (1 + |a| + a^2)^3 ≥ (1 + |a|)^3 * (1 + |a|^3)   := by
  have hs : 0 ≤ 3 * |a|^4 + 5 * |a|^3 + 3 * |a|^2 := by positivity
  have hi : ( (1 + |a| + a^2)^3 ) - ( (1 + |a|)^3 * (1 + |a|^3)   ) = 3 * |a|^4 + 5 * |a|^3 + 3 * |a|^2 := by
    rw [← sq_abs a]
    ring
  linarith only [hs,hi]
example : (∀ (a : ℝ), (1 + |a| + a^2)^3 ≥ (1 + |a|)^3 * (1 + |a|^3)) := @solution
#print axioms solution
