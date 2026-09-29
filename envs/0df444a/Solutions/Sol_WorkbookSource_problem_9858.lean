-- Prove2me | solution 1 for WorkbookSource.problem_9858
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:15.533341+00:00
-- url     : https://prove2.me/submissions/820e805a-38ab-4d7f-bc65-58b730d9b143

/- InternLM Lean-Workbook, lean_workbook_9858, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℕ → ℝ) (hx : Monotone x) : (x 1 + x 2 + x 3 + x 4 + x 5 + x 6) / 6 ≤ (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9 + x 10) / 10  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [hx (by norm_num : 1 ≤ 2), hx (by norm_num : 2 ≤ 3), hx (by norm_num : 3 ≤ 4), hx (by norm_num : 4 ≤ 5), hx (by norm_num : 5 ≤ 6), hx (by norm_num : 6 ≤ 7), hx (by norm_num : 7 ≤ 8), hx (by norm_num : 8 ≤ 9), hx (by norm_num : 9 ≤ 10)]
  | solve
    | norm_num
      linarith [hx (by norm_num : 1 ≤ 2), hx (by norm_num : 2 ≤ 3), hx (by norm_num : 3 ≤ 4), hx (by norm_num : 4 ≤ 5), hx (by norm_num : 5 ≤ 6), hx (by norm_num : 6 ≤ 7), hx (by norm_num : 7 ≤ 8), hx (by norm_num : 8 ≤ 9), hx (by norm_num : 9 ≤ 10)]
  | solve
    | nlinarith [hx (by norm_num : 1 ≤ 2), hx (by norm_num : 2 ≤ 3), hx (by norm_num : 3 ≤ 4), hx (by norm_num : 4 ≤ 5), hx (by norm_num : 5 ≤ 6), hx (by norm_num : 6 ≤ 7), hx (by norm_num : 7 ≤ 8), hx (by norm_num : 8 ≤ 9), hx (by norm_num : 9 ≤ 10)]
  | solve
    | norm_num
      nlinarith [hx (by norm_num : 1 ≤ 2), hx (by norm_num : 2 ≤ 3), hx (by norm_num : 3 ≤ 4), hx (by norm_num : 4 ≤ 5), hx (by norm_num : 5 ≤ 6), hx (by norm_num : 6 ≤ 7), hx (by norm_num : 7 ≤ 8), hx (by norm_num : 8 ≤ 9), hx (by norm_num : 9 ≤ 10)]
example : (∀ (x : ℕ → ℝ) (hx : Monotone x), (x 1 + x 2 + x 3 + x 4 + x 5 + x 6) / 6 ≤ (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9 + x 10) / 10) := @solution
#print axioms solution
