-- Prove2me | solution 1 for WorkbookSource.plus_34677
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:14.419386+00:00
-- url     : https://prove2.me/submissions/01516a66-eee0-4c92-a40f-14835d3e8047

/- InternLM Lean-Workbook, lean_workbook_plus_34677, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) : (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2 + 3) ≤ 1 → a * b + b * c + c * a ≤ 3 / 2   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [div_le_iff]
      intro h
      linarith
      nlinarith
  | solve
    | intro h
      rw [div_le_one] at h
      linarith
      nlinarith
  | solve
    | intro h
      rw [div_le_one] at h
      linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
      nlinarith
example : (∀ (a b c : ℝ), (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2 + 3) ≤ 1 → a * b + b * c + c * a ≤ 3 / 2) := @solution
#print axioms solution
