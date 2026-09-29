-- Prove2me | solution 1 for WorkbookSource.problem_39348
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:44.48486+00:00
-- url     : https://prove2.me/submissions/ade5a6c4-9b41-4e8f-89e3-c74068d9faf8

/- InternLM Lean-Workbook, lean_workbook_39348, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (h : a + b + c = 0) : b = -a - c  := by
  first
  | solve
    | linarith
  | solve
    | simp [add_comm a b, add_comm c a, add_comm c b] at h ⊢
      linarith
  | solve
    | rw [← add_right_inj c]
      linarith only [h]
  | solve
    | simp [add_comm] at h ⊢
      linarith
  | solve
    | rw [add_assoc] at h
      linarith [h]
  | solve
    | rw [add_comm] at h
      linarith
  | solve
    | rw [← add_right_inj c] at h
      linarith
  | solve
    | simp only [add_assoc] at h
      linarith
  | solve
    | rw [add_assoc] at h
      linarith
  | solve
    | simp [add_comm, add_left_comm, sub_eq_add_neg] at h ⊢
      linarith
  | solve
    | apply eq_of_sub_eq_zero
      linear_combination h
  | solve
    | field_simp [add_assoc, add_comm, add_left_comm] at h ⊢
      linarith
  | solve
    | rw [← sub_eq_zero] at h
      linarith
  | solve
    | rw [← sub_eq_zero]
      linarith only [h]
  | solve
    | rw [add_assoc] at h
      rw [← sub_eq_zero]
      linarith
  | solve
    | simp only [add_assoc] at h ⊢
      linarith [h]
  | solve
    | simp only [add_eq_zero_iff_eq_neg] at h
      linarith [h]
  | solve
    | simp only [add_assoc] at h ⊢
      linarith
  | solve
    | linarith [h, h]
  | solve
    | rw [add_assoc] at h
      rw [← sub_eq_zero] at h ⊢
      linarith
  | solve
    | ring_nf at h ⊢
      linarith
  | solve
    | rw [← sub_eq_zero]
      linarith
example : (∀ (a b c : ℝ) (h : a + b + c = 0), b = -a - c) := @solution
#print axioms solution
