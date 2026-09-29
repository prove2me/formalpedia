-- Prove2me | solution 1 for WorkbookSource.problem_40509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:51.657274+00:00
-- url     : https://prove2.me/submissions/a193e311-9b0c-4e93-b060-42779dc42eb7

/- InternLM Lean-Workbook, lean_workbook_40509, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ a b c : ℝ, (a^3 / (b^3 + c^3) : ℝ) = (a / (b + c) : ℝ) * (a^2 / (b^2 + c^2 - b * c) : ℝ)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro a b c
      field_simp
      ring
  | solve
    | intro a b c
      field_simp [mul_comm]
      ring
  | solve
    | intros a b c
      field_simp [add_comm]
      ring
  | solve
    | refine' fun a b c => by field_simp [add_comm]; ring
example : (∀ a b c : ℝ, (a^3 / (b^3 + c^3) : ℝ) = (a / (b + c) : ℝ) * (a^2 / (b^2 + c^2 - b * c) : ℝ)) := @solution
#print axioms solution
