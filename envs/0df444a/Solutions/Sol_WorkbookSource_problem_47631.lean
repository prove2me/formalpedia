-- Prove2me | solution 1 for WorkbookSource.problem_47631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:10.599656+00:00
-- url     : https://prove2.me/submissions/af68b14e-a513-4bf0-bcb2-32c07ad58d98

/- InternLM Lean-Workbook, lean_workbook_47631, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Complex
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ b z:ℂ, z^2 * b^2 + z * b - 2 = (b * z - 1) * (b * z + 2)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rintro b z
      ring
  | solve
    | rintro b z
      ring_nf
  | solve
    | intros b z
      ring_nf
  | solve
    | simp [sq]
      intros
      ring
  | solve
    | repeat' intro b z; ring
example : (∀ b z:ℂ, z^2 * b^2 + z * b - 2 = (b * z - 1) * (b * z + 2)) := @solution
#print axioms solution
