-- Prove2me | solution 1 for WorkbookSource.problem_14193
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:30.748156+00:00
-- url     : https://prove2.me/submissions/2a8031d0-fe0e-4aac-b3aa-40c3326e9851

/- InternLM Lean-Workbook, lean_workbook_14193, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (hf : ∀ x, 2 * f x + 3 * f (2010 / x) = 5 * x) : f 6 = 993  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have := hf 6
      have := hf (2010/6)
      norm_num at *
      linarith
  | solve
    | have h₁ := hf 6
      have h₂ := hf (2010 / 6)
      norm_num at *
      linarith
  | solve
    | have h₁ := hf 6
      have h₂ := hf (2010/6)
      norm_num at h₁ h₂
      linarith
  | solve
    | have h₁ := hf 6
      have h₂ := hf (2010 / 6)
      norm_num at *
      linarith [h₁, h₂]
  | solve
    | have := hf 6
      have := hf (2010/6)
      norm_num at *
      nlinarith
  | solve
    | have h₁ := hf 6
      have h₂ := hf (2010 / 6)
      norm_num at *
      nlinarith
  | solve
    | have h₁ := hf 6
      have h₂ := hf (2010/6)
      norm_num at h₁ h₂
      nlinarith
  | solve
    | have h₁ := hf 6
      have h₂ := hf (2010 / 6)
      norm_num at *
      nlinarith [h₁, h₂]
example : (∀ (f : ℝ → ℝ) (hf : ∀ x, 2 * f x + 3 * f (2010 / x) = 5 * x), f 6 = 993) := @solution
#print axioms solution
