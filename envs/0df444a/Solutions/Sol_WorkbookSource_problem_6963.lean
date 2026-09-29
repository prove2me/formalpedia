-- Prove2me | solution 1 for WorkbookSource.problem_6963
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:31.340897+00:00
-- url     : https://prove2.me/submissions/9e74e006-dca9-4831-8591-71100b3b3c34

/- InternLM Lean-Workbook, lean_workbook_6963, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0) :
  (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2 + (1 / 9) * (a + b + c) ^ 2) ≤ 9 / (4 * (a + b + c))  := by
  have hs : 0 < a + b + c := by linarith [h.1,h.2.1,h.2.2]
  have hd : 0 < a ^ 2 + b ^ 2 + c ^ 2 + (1 / 9) * (a + b + c) ^ 2 := by positivity
  apply (div_le_div_iff₀ hd (by positivity)).2
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
example : (∀ (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0), (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2 + (1 / 9) * (a + b + c) ^ 2) ≤ 9 / (4 * (a + b + c))) := @solution
#print axioms solution
