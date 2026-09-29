-- Prove2me | solution 1 for WorkbookSource.problem_29260
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:19.349188+00:00
-- url     : https://prove2.me/submissions/cac90cd6-fe36-41a1-a077-70a101d91344

/- InternLM Lean-Workbook, lean_workbook_29260, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ a b c : ℝ, a * b * c = b * c * a → a^3 * (b - c) + b^3 * (c - a) + c^3 * (a - b) = (b - a) * (c * (b^2 + b * a + a^2) - b * a * (b + a) - c^3)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intros; ring_nf
  | solve
    | intros
      simp [*, mul_sub, sub_mul]
      ring
  | solve
    | intros a b c h
      field_simp [mul_assoc]
      ring
  | solve
    | intro a b c h
      field_simp [h, pow_three]
      ring
example : (∀ a b c : ℝ, a * b * c = b * c * a → a^3 * (b - c) + b^3 * (c - a) + c^3 * (a - b) = (b - a) * (c * (b^2 + b * a + a^2) - b * a * (b + a) - c^3)) := @solution
#print axioms solution
