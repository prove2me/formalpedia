-- Prove2me | solution 1 for WorkbookSource.problem_48567
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:52.038875+00:00
-- url     : https://prove2.me/submissions/24fb856d-d387-4ae6-9867-4439f428910b

/- InternLM Lean-Workbook, lean_workbook_48567, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (b + c + a) + b / (c + a + b) + c / (a + b + c) < 3 / 2  := by
  have hs : a + b + c ≠ 0 := ne_of_gt (by positivity)
  have hbc : b + c + a = a + b + c := by ring
  have hca : c + a + b = a + b + c := by ring
  rw [hbc, hca]
  rw [← add_div, ← add_div, div_self hs]
  norm_num

example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a / (b + c + a) + b / (c + a + b) + c / (a + b + c) < 3 / 2) := @solution
#print axioms solution
