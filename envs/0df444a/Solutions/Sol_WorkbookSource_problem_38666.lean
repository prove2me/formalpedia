-- Prove2me | solution 1 for WorkbookSource.problem_38666
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:48.265231+00:00
-- url     : https://prove2.me/submissions/46bf8dfa-5f30-4cb9-968f-3f656e535053

/- InternLM Lean-Workbook, lean_workbook_38666, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y z : ℝ) (hx : x = 2^110) (hy : y = 3^75) (hz : z = 5^49) : y > z ∧ z > x  := by
  first
  | solve
    | rw [hx,hy,hz]
      norm_num
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [hx, hy, hz]
  | solve
    | norm_num [hy, hz, hx]
  | solve
    | substs hx hy hz
      norm_num
  | solve
    | rw [hy, hz]
      rw [hx]
      norm_num
example : (∀ (x y z : ℝ) (hx : x = 2^110) (hy : y = 3^75) (hz : z = 5^49), y > z ∧ z > x) := @solution
#print axioms solution
