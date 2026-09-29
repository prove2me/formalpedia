-- Prove2me | solution 1 for WorkbookSource.problem_7260
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:32.159234+00:00
-- url     : https://prove2.me/submissions/77204dc8-92e0-49f2-80fe-40e717158b20

/- InternLM Lean-Workbook, lean_workbook_7260, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f g : ℝ → ℝ) (hf : ∀ x, f x = 3 * x ^ 2 - 7) (hg : g (f 4) = 9) : g (f (-4)) = 9  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [hf] at hg ⊢
      linarith
  | solve
    | simp [hf, hg] at *
      linarith
  | solve
    | simp [hf] at hg ⊢
      linarith [hg]
  | solve
    | rw [hf] at hg
      rw [hf]
      simp [hg]
  | solve
    | simp [hf] at hg ⊢
      nlinarith
  | solve
    | simp [hf, hg] at *
      nlinarith
  | solve
    | simp [hf] at hg ⊢
      nlinarith [hg]
example : (∀ (f g : ℝ → ℝ) (hf : ∀ x, f x = 3 * x ^ 2 - 7) (hg : g (f 4) = 9), g (f (-4)) = 9) := @solution
#print axioms solution
