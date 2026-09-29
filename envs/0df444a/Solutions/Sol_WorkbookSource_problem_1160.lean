-- Prove2me | solution 1 for WorkbookSource.problem_1160
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:58.532452+00:00
-- url     : https://prove2.me/submissions/8007bb09-dde4-4863-89b2-61784790a7c9

/- InternLM Lean-Workbook, lean_workbook_1160, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [ha, hb, hc]
  | solve
    | norm_num at *
      linarith
  | solve
    | ring_nf at ha hb hc
      linarith
  | solve
    | simp [mul_comm] at *
      linarith
  | solve
    | nlinarith [ha, hb, hc]
  | solve
    | norm_num at *
      nlinarith
  | solve
    | ring_nf at ha hb hc
      nlinarith
  | solve
    | simp [mul_comm] at *
      nlinarith
example : (∀ (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49), 16 * a + 25 * b + 36 * c + 49 * d = 64) := @solution
#print axioms solution
