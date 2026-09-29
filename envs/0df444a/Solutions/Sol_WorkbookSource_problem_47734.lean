-- Prove2me | solution 1 for WorkbookSource.problem_47734
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:55.844267+00:00
-- url     : https://prove2.me/submissions/8dc204bb-f19a-4691-8138-8d26f2d89d9b

/- InternLM Lean-Workbook, lean_workbook_47734, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : (x + 1 / x - z / y)^2 + (y + 1 / y - x / z)^2 + (z + 1 / z - y / x)^2 + (x + 1 / x - z / y) * (y + 1 / y - x / z) * (z + 1 / z - y / x) = 4  := by
  have hxval : x = 1 / y / z := by rw [← h]; field_simp
  rw [hxval]
  field_simp
  ring

example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1), (x + 1 / x - z / y)^2 + (y + 1 / y - x / z)^2 + (z + 1 / z - y / x)^2 + (x + 1 / x - z / y) * (y + 1 / y - x / z) * (z + 1 / z - y / x) = 4) := @solution
#print axioms solution
