-- Prove2me | solution 1 for WorkbookSource.problem_15372
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:34.210978+00:00
-- url     : https://prove2.me/submissions/f4787225-9fea-460d-8544-669103300438

/- InternLM Lean-Workbook, lean_workbook_15372, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀x, f x = 2 * x + 1 / 3) :
  f 0 = 1 / 3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [h₀]
  | solve
    | rw [h₀]
      simp
  | solve
    | rw [h₀]
      ring
  | solve
    | norm_num [h₀]
example : (∀ (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀x, f x = 2 * x + 1 / 3), f 0 = 1 / 3) := @solution
#print axioms solution
