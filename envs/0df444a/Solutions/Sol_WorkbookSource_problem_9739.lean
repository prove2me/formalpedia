-- Prove2me | solution 1 for WorkbookSource.problem_9739
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:13.874634+00:00
-- url     : https://prove2.me/submissions/3460878a-eb8e-4bbd-a055-d51084f7320e

/- InternLM Lean-Workbook, lean_workbook_9739, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x + 1/x * f (-1/x) = 3) : f 2 = 3/4  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have := hf 2
      have := hf (-1/2)
      field_simp at *
      linarith
  | solve
    | have h1 := hf 2
      have h2 := hf (-1/2)
      norm_num at *
      linarith
  | solve
    | have H := hf 2
      have H' := hf (-1/2)
      field_simp at H H'
      linarith
  | solve
    | have h₁ := hf 2
      have h₂ := hf (-1/2)
      field_simp at h₁ h₂
      linarith
  | solve
    | have := hf 2
      have := hf (-1/2)
      field_simp at *
      nlinarith
  | solve
    | have h1 := hf 2
      have h2 := hf (-1/2)
      norm_num at *
      nlinarith
  | solve
    | have H := hf 2
      have H' := hf (-1/2)
      field_simp at H H'
      nlinarith
  | solve
    | have h₁ := hf 2
      have h₂ := hf (-1/2)
      field_simp at h₁ h₂
      nlinarith
example : (∀ (f : ℝ → ℝ) (hf : ∀ x, f x + 1/x * f (-1/x) = 3), f 2 = 3/4) := @solution
#print axioms solution
