-- Prove2me | solution 1 for WorkbookSource.problem_140
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:53.641463+00:00
-- url     : https://prove2.me/submissions/fa178552-c8bd-4c2b-8e69-59c2a6d6e274

/- InternLM Lean-Workbook, lean_workbook_140, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [sq]
      ring_nf
      field_simp
      ring_nf
  | solve
    | ring_nf
      rw [Real.sq_sqrt] <;> linarith
  | solve
    | rw [add_mul]
      ring_nf
      field_simp
      ring_nf
  | solve
    | rw [mul_comm]
      ring_nf
      field_simp
      ring_nf
  | solve
    | ring_nf
      rw [Real.sq_sqrt] <;> nlinarith
example : (∀ (x : ℝ), x^2 + 4*x - 1 = (x + 2 + Real.sqrt 5) * (x + 2 - Real.sqrt 5)) := @solution
#print axioms solution
