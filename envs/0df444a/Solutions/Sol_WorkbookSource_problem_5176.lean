-- Prove2me | solution 1 for WorkbookSource.problem_5176
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:08.873035+00:00
-- url     : https://prove2.me/submissions/e565b2bd-7b67-4764-9695-57ace5f63385

/- InternLM Lean-Workbook, lean_workbook_5176, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (ha : 0 < a ∧ a ≤ 1 / 2) (hb : 0 < b ∧ b ≤ 1 / 2) (hc : 0 < c ∧ c ≤ 1 / 2) (hab : a + b + c = 1) : 2 * a + 3 * b + 4 * c ≥ 5 / 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [ha, hb, hc, hab]
  | solve
    | linarith [ha.2, hb.2, hc.2]
  | solve
    | rw [add_comm] at hab
      linarith
  | solve
    | linarith only [ha, hb, hc, hab]
  | solve
    | nlinarith [ha, hb, hc, hab]
  | solve
    | nlinarith [ha.2, hb.2, hc.2]
  | solve
    | rw [add_comm] at hab
      nlinarith
  | solve
    | nlinarith only [ha, hb, hc, hab]
example : (∀ (a b c : ℝ) (ha : 0 < a ∧ a ≤ 1 / 2) (hb : 0 < b ∧ b ≤ 1 / 2) (hc : 0 < c ∧ c ≤ 1 / 2) (hab : a + b + c = 1), 2 * a + 3 * b + 4 * c ≥ 5 / 2) := @solution
#print axioms solution
