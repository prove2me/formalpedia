-- Prove2me | solution 1 for WorkbookSource.problem_49830
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:56.583211+00:00
-- url     : https://prove2.me/submissions/46fd1b96-a3e2-4cb8-8391-d19a92761ec2

/- InternLM Lean-Workbook, lean_workbook_49830, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (x : ℝ) (f_def : f x = x^2 - 2*x) : f x = 0 ↔ x = 0 ∨ x = 2  := by
  first
  | solve
    | rw [f_def]
      have he : x^2-2*x=x*(x-2) := by ring
      rw [he,mul_eq_zero,sub_eq_zero]
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [f_def]
      simp [sub_eq_zero, sq]
      aesop
  | solve
    | rw [f_def]
      simp [sub_eq_zero, sq]
      ring_nf
      aesop
  | solve
    | simp [f_def, sub_eq_zero, sq, mul_self_eq_mul_self_iff]
      aesop
  | solve
    | simp [f_def, sq, sub_eq_zero]
      constructor <;> intro h <;> aesop
example : (∀ (f : ℝ → ℝ) (x : ℝ) (f_def : f x = x^2 - 2*x), f x = 0 ↔ x = 0 ∨ x = 2) := @solution
#print axioms solution
