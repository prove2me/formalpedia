-- Prove2me | solution 1 for WorkbookSource.problem_56689
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:57.397729+00:00
-- url     : https://prove2.me/submissions/277001af-ddae-4b27-8f92-72cbdb8d45f1

/- InternLM Lean-Workbook, lean_workbook_56689, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a : ℝ) (h : a = 2009) : |2*a^3 - 3*a^2 - 2*a + 1| - |2*a^3 - 3*a^2 - 3*a - 2009| = 4019  := by
  first
  | solve
    | rw [h]
      norm_num
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [h]
  | solve
    | rw [h]
      norm_num
  | solve
    | rw [h]
      norm_num [h]
  | solve
    | simp [h]
      norm_num [h]
example : (∀ (a : ℝ) (h : a = 2009), |2*a^3 - 3*a^2 - 2*a + 1| - |2*a^3 - 3*a^2 - 3*a - 2009| = 4019) := @solution
#print axioms solution
