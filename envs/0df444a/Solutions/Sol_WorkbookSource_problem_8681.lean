-- Prove2me | solution 1 for WorkbookSource.problem_8681
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:07.463874+00:00
-- url     : https://prove2.me/submissions/e64494f7-6f4a-4d6c-b4cb-59e6c1dfbaa8

/- InternLM Lean-Workbook, lean_workbook_8681, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a r n : ℝ) (ha : a = 2) (hr : r = 1/3) (hn : n = 2) : a + a*r = 8/3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | subst a r n
      ring
  | solve
    | subst ha hr hn
      ring
  | solve
    | subst ha hr hn
      ring_nf
  | solve
    | simp [ha, hr, hn]
      ring
example : (∀ (a r n : ℝ) (ha : a = 2) (hr : r = 1/3) (hn : n = 2), a + a*r = 8/3) := @solution
#print axioms solution
