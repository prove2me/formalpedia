-- Prove2me | solution 1 for WorkbookSource.problem_39372
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:46.010822+00:00
-- url     : https://prove2.me/submissions/dd0eaefd-8768-47aa-a3b9-d2777d480934

/- InternLM Lean-Workbook, lean_workbook_39372, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (f : ℝ → ℝ) (h : 4 * f (-1) = 2 * f (-1) + 2) : f (-1) = 1  := by
  first
  | solve
    | linarith
  | solve
    | rw [← sub_eq_zero]
      linarith
  | solve
    | norm_num at h
      linarith [h]
  | solve
    | have h1 : 4 * f (-1) = 2 * f (-1) + 2 := h
      ring_nf at h1
      linarith
  | solve
    | nlinarith [h, show (4 : ℝ) ≠ 0 by norm_num]
  | solve
    | simp [mul_comm] at h
      linarith
  | solve
    | ring_nf at h ⊢
      norm_num at h
      linarith [h]
  | solve
    | linarith [h]
  | solve
    | nlinarith [h, show (4 : ℝ) ≠ 0 by norm_num, show (2 : ℝ) ≠ 0 by norm_num]
  | solve
    | ring_nf at h ⊢
      linarith [h]
  | solve
    | rw [eq_comm] at h
      linarith [h]
  | solve
    | norm_num at h ⊢
      linarith [h]
  | solve
    | rw [← mul_right_inj' (two_ne_zero' ℝ)] at h
      linarith
  | solve
    | ring_nf at h
      linarith [h]
  | solve
    | rw [mul_comm] at h
      linarith only [h]
example : (∀ (f : ℝ → ℝ) (h : 4 * f (-1) = 2 * f (-1) + 2), f (-1) = 1) := @solution
#print axioms solution
