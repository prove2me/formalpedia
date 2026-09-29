-- Prove2me | solution 1 for WorkbookSource.problem_11015
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:24.476022+00:00
-- url     : https://prove2.me/submissions/8664c01d-6fdd-45fb-89ce-d584a341996d

/- InternLM Lean-Workbook, lean_workbook_11015, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y : ℝ) (h₁ : x + 2 * y = 9) (h₂ : x ≥ y) : (x + y) ^ 2 / (2 * (x + y) + 27) ≥ 2 * (x + y) / 13  := by
  have hs : 6 ≤ x + y := by linarith
  have hd : 0 < 2 * (x + y) + 27 := by linarith
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ) < 13) hd).2
  nlinarith [mul_nonneg (show 0 ≤ x+y by linarith) (show 0 ≤ x+y-6 by linarith)]
example : (∀ (x y : ℝ) (h₁ : x + 2 * y = 9) (h₂ : x ≥ y), (x + y) ^ 2 / (2 * (x + y) + 27) ≥ 2 * (x + y) / 13) := @solution
#print axioms solution
