-- Prove2me | solution 1 for WorkbookSource.problem_7831
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:34.083817+00:00
-- url     : https://prove2.me/submissions/479a24f3-3fa0-4b05-88bf-ac8c503059bb

/- InternLM Lean-Workbook, lean_workbook_7831, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (2^3000:ℝ) < 3^2000  := by
  have h : (8 : ℝ)^1000 < 9^1000 := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by norm_num)
  have h2 : (2 : ℝ)^3000 = 8^1000 := by rw [show 3000 = 3 * 1000 by omega, pow_mul]; norm_num
  have h3 : (3 : ℝ)^2000 = 9^1000 := by rw [show 2000 = 2 * 1000 by omega, pow_mul]; norm_num
  rw [h2,h3]
  exact h
example : ((2^3000:ℝ) < 3^2000) := @solution
#print axioms solution
