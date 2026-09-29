-- Prove2me | solution 1 for WorkbookSource.problem_49227
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:53.508369+00:00
-- url     : https://prove2.me/submissions/d8270632-468c-4dee-a353-b3e3ec7c8e68

/- InternLM Lean-Workbook, lean_workbook_49227, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 3) : 3 * a ^ 2 + 3 * b ^ 2 + c ^ 3 ≤ 27  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [pow_two, pow_three]
      nlinarith
  | solve
    | nlinarith [ha, hb, hc, pow_three c, habc]
  | solve
    | simp [pow_two, pow_three, mul_add, add_mul]
      nlinarith
  | solve
    | simp [pow_two, pow_three]
      nlinarith [habc, ha, hb, hc]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 3), 3 * a ^ 2 + 3 * b ^ 2 + c ^ 3 ≤ 27) := @solution
#print axioms solution
