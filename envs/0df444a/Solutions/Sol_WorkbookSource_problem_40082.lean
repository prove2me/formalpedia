-- Prove2me | solution 1 for WorkbookSource.problem_40082
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:46.733721+00:00
-- url     : https://prove2.me/submissions/f3ea01f6-029d-42f0-80a6-c561863d7610

/- InternLM Lean-Workbook, lean_workbook_40082, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {a b c : ℝ} : (a^2 / b^3 - 1 / a) + (b^2 / c^3 - 1 / b) + (c^2 / a^3 - 1 / c) = (a^2 / b^3 - 1 / b) + (b^2 / c^3 - 1 / c) + (c^2 / a^3 - 1 / a)  := by
  first
  | solve
    | ring
  | solve
    | linarith [a^2 / b^3, 1 / a, 1 / b, b^2 / c^3, c^2 / a^3]
  | solve
    | linarith [a, b, c]
  | solve
    | rw [add_comm]
      ring_nf
  | solve
    | rw [add_comm]
      ring
  | solve
    | simp [add_assoc, add_comm, add_left_comm]
      ring
  | solve
    | nlinarith [a, b, c]
  | solve
    | simp only [add_comm, add_left_comm]
      ring
  | solve
    | linear_combination 1 / a
  | solve
    | simp only [add_assoc, add_comm, add_left_comm]
      ring
  | solve
    | ring_nf at *
  | solve
    | simp only [sub_eq_add_neg, add_assoc, add_left_comm]
      ring_nf
example : (∀ {a b c : ℝ}, (a^2 / b^3 - 1 / a) + (b^2 / c^3 - 1 / b) + (c^2 / a^3 - 1 / c) = (a^2 / b^3 - 1 / b) + (b^2 / c^3 - 1 / c) + (c^2 / a^3 - 1 / a)) := @solution
#print axioms solution
