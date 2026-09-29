-- Prove2me | solution 1 for WorkbookSource.problem_16058
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:13.563543+00:00
-- url     : https://prove2.me/submissions/c8801839-7ddb-4386-8611-70d5dcf3f081

/- InternLM Lean-Workbook, lean_workbook_16058, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y : ℝ) (hx : x = (101!)^100) (hy : y = (100!)^101) : x > y  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [hy, hx]
      norm_cast
  | solve
    | simp [hx, hy]
      norm_cast
  | solve
    | simp [hx, hy, factorial]
      norm_num
  | solve
    | rw [hx, hy]
      clear hx hy
      norm_cast
example : (∀ (x y : ℝ) (hx : x = (101!)^100) (hy : y = (100!)^101), x > y) := @solution
#print axioms solution
