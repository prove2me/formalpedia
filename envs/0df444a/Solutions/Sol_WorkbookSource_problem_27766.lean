-- Prove2me | solution 1 for WorkbookSource.problem_27766
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:45.174825+00:00
-- url     : https://prove2.me/submissions/77936bb0-dd1f-4398-bab4-f40f2a3211dd

/- InternLM Lean-Workbook, lean_workbook_27766, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c d e : ℝ) : (a + b + c + d + e) ^ 2 - (5 / 2) * (a * (b + c) + b * (c + d) + c * (d + e) + d * (e + a) + e * (a + b))  = (1 / 16) * (4 * e - d - c - b - a) ^ 2 + (15 / 144) * (3 * d - c - b - a) ^ 2 + (5 / 24) * (2 * c - b - a) ^ 2 + (5 / 8) * (b - a) ^ 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [pow_two]
      ring
  | solve
    | norm_num [pow_two]
      ring
  | solve
    | field_simp [add_assoc]
      ring
  | solve
    | simp [mul_add, add_mul]
      ring_nf
example : (∀ (a b c d e : ℝ), (a + b + c + d + e) ^ 2 - (5 / 2) * (a * (b + c) + b * (c + d) + c * (d + e) + d * (e + a) + e * (a + b))  = (1 / 16) * (4 * e - d - c - b - a) ^ 2 + (15 / 144) * (3 * d - c - b - a) ^ 2 + (5 / 24) * (2 * c - b - a) ^ 2 + (5 / 8) * (b - a) ^ 2) := @solution
#print axioms solution
