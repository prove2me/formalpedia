-- Prove2me | solution 1 for WorkbookSource.problem_22623
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:44.421337+00:00
-- url     : https://prove2.me/submissions/e84db598-974b-4a89-8cc4-b0bdf1581864

/- InternLM Lean-Workbook, lean_workbook_22623, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c d : ℝ) : (Real.log b / Real.log a) * (Real.log d / Real.log c) = (Real.log d / Real.log a) * (Real.log b / Real.log c)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [mul_comm]
      field_simp
      ring
  | solve
    | field_simp [← Real.log_mul]
      ring
  | solve
    | simp only [div_eq_mul_inv, mul_right_comm]
      ring_nf
  | solve
    | simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
example : (∀ (a b c d : ℝ), (Real.log b / Real.log a) * (Real.log d / Real.log c) = (Real.log d / Real.log a) * (Real.log b / Real.log c)) := @solution
#print axioms solution
