-- Prove2me | solution 1 for WorkbookSource.problem_7972
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:11.82845+00:00
-- url     : https://prove2.me/submissions/782db149-8426-47c8-afa5-e66dd833b81b

/- InternLM Lean-Workbook, lean_workbook_7972, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c x y z: ℝ) : (a ^ 2 + x ^ 2) * (b ^ 2 + y ^ 2) * (c ^ 2 + z ^ 2) = (a * y * z + b * x * z + c * x * y - a * b * c) ^ 2 + (x * b * c + y * a * c + z * a * b - x * y * z) ^ 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [sq]
      ring_nf
  | solve
    | simp [pow_two]
      ring
  | solve
    | simp only [sq]
      ring
  | solve
    | repeat rw [sq]; ring
example : (∀ (a b c x y z: ℝ), (a ^ 2 + x ^ 2) * (b ^ 2 + y ^ 2) * (c ^ 2 + z ^ 2) = (a * y * z + b * x * z + c * x * y - a * b * c) ^ 2 + (x * b * c + y * a * c + z * a * b - x * y * z) ^ 2) := @solution
#print axioms solution
