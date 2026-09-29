-- Prove2me | solution 1 for WorkbookSource.problem_47872
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:51.305877+00:00
-- url     : https://prove2.me/submissions/a40a327b-f151-4a9f-a043-26a402c501d6

/- InternLM Lean-Workbook, lean_workbook_47872, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a : ℝ) (ha : a ≥ 0) : a^3 / (a^4 + 1) ≤ a / 2  := by
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [mul_nonneg ha (sq_nonneg (a^2 - 1))]

example : (∀ (a : ℝ) (ha : a ≥ 0), a^3 / (a^4 + 1) ≤ a / 2) := @solution
#print axioms solution
