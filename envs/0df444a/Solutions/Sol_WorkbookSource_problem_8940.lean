-- Prove2me | solution 1 for WorkbookSource.problem_8940
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:09.069913+00:00
-- url     : https://prove2.me/submissions/73011e9d-1be5-4f39-9275-91720c6540e9

/- InternLM Lean-Workbook, lean_workbook_8940, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (x y : ℝ)
  (h₀ : 2 * x + y ≥ 2) :
  (2 * x + y)^2 + (2 * y - x)^2 ≥ 4  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [sq]
      nlinarith
  | solve
    | rw [sq, sq]
      nlinarith
  | solve
    | simp [sq, h₀]
      nlinarith
  | solve
    | norm_cast at h₀ ⊢
      nlinarith
example : (∀ (x y : ℝ)
  (h₀ : 2 * x + y ≥ 2), (2 * x + y)^2 + (2 * y - x)^2 ≥ 4) := @solution
#print axioms solution
