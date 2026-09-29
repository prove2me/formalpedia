-- Prove2me | solution 1 for WorkbookSource.problem_34929
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:53.511985+00:00
-- url     : https://prove2.me/submissions/ca379910-2b4d-4e7d-a839-e4e8125fb677

/- InternLM Lean-Workbook, lean_workbook_34929, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2 + 4 * (x ^ 2 + y * z + x * z + y * x) = 128 → x ^ 2 + y ^ 2 + z ^ 2 + 3 * (x * y + x * z + y * z) = 64 - 2 * x ^ 2  := by
  first
  | solve
    | intro h
      nlinarith
  | solve
    | intro h
      linarith
  | solve
    | intro h
      nlinarith
  | solve
    | intros h
      linarith
  | solve
    | intro h
      simp only [sq] at h ⊢
      linarith
  | solve
    | field_simp [pow_two]
      intro h
      linarith [h]
  | solve
    | field_simp [add_comm, add_left_comm, add_assoc]
      intro h
      linarith
  | solve
    | intro h
      simp [sq, mul_add, add_mul] at h ⊢
      linarith
  | solve
    | rintro h
      linarith [h]
  | solve
    | simp [pow_two]
      intro h
      linarith
  | solve
    | intro h
      linarith only [h]
  | solve
    | intro h
      simp only [sq] at *
      linarith
  | solve
    | intro h
      ring_nf at h
      linarith [h]
  | solve
    | simp [sq, add_mul, mul_add, mul_comm, mul_left_comm]
      intro h
      linarith
  | solve
    | intro h
      ring_nf at h ⊢
      linarith
  | solve
    | intro h
      ring_nf at h ⊢
      norm_num at h ⊢
      linarith [h]
  | solve
    | intro h
      simp [add_assoc, add_comm, add_left_comm] at *
      linarith
  | solve
    | intro h
      rw [add_assoc] at h
      linarith
  | solve
    | ring_nf
      intro h
      linarith [h]
example : (∀ (x y z : ℝ), (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2 + 4 * (x ^ 2 + y * z + x * z + y * x) = 128 → x ^ 2 + y ^ 2 + z ^ 2 + 3 * (x * y + x * z + y * z) = 64 - 2 * x ^ 2) := @solution
#print axioms solution
