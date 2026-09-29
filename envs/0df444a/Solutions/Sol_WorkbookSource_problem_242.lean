-- Prove2me | solution 1 for WorkbookSource.problem_242
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:54.552637+00:00
-- url     : https://prove2.me/submissions/e3767223-0780-4c7c-90dc-3f48d2b0f95b

/- InternLM Lean-Workbook, lean_workbook_242, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (x y a : ℝ) :
  (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor <;> intro h <;> linarith
  | solve
    | rw [sq]
      constructor <;> intro h <;> linarith
  | solve
    | ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | constructor <;> intro h
      linarith [h]
      nlinarith
  | solve
    | constructor <;> intro h <;> nlinarith
  | solve
    | rw [sq]
      constructor <;> intro h <;> nlinarith
  | solve
    | ring_nf
      constructor <;> intro h <;> nlinarith
example : (∀ (x y a : ℝ), (3 * a + 2 * x + y) ^ 2 ≤ 9 * (a + x) * (a + x + y) ↔ 3 * a * (2 * x + y) + 5 * x ^ 2 + 5 * x * y ≥ y ^ 2) := @solution
#print axioms solution
