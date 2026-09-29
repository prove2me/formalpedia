-- Prove2me | solution 1 for WorkbookSource.problem_2542
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:01.674417+00:00
-- url     : https://prove2.me/submissions/a09b2178-1796-4736-af0f-0670060941ff

/- InternLM Lean-Workbook, lean_workbook_2542, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (hf : ∀ x, f (f x) = x + 1) : Function.Bijective f  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor
      intro x₁ x₂ h
      apply_fun f at h
      simpa [hf] using h
      intro x
      use f (x - 1)
      simp [hf]
  | solve
    | constructor
      intro a b hab
      apply_fun f at hab
      simpa [hf] using hab
      intro y
      use f (y - 1)
      simp [hf]
  | solve
    | constructor
      intro a b hab
      apply_fun f at hab
      simpa [hf] using hab
      intro b
      use f (b - 1)
      simp [hf]
  | solve
    | constructor
      intro x y hxy
      apply_fun f at hxy
      simpa [hf] using hxy
      intro y
      use f (y - 1)
      simp [hf]
example : (∀ (f : ℝ → ℝ) (hf : ∀ x, f (f x) = x + 1), Function.Bijective f) := @solution
#print axioms solution
