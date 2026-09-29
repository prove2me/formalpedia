-- Prove2me | solution 1 for WorkbookSource.problem_13032
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:24.2409+00:00
-- url     : https://prove2.me/submissions/8c4c6d2c-1a0b-4ab8-a564-db4b734d1974

/- InternLM Lean-Workbook, lean_workbook_13032, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c d : ℝ) (h₁ : a*0^3 + b*0^2 + c*0 + d = 4) (h₂ : a*1^3 + b*1^2 + c*1 + d = 10) (h₃ : a*2^3 + b*2^2 + c*2 + d = 26) (h₄ : a*(-1)^3 + b*(-1)^2 + c*(-1) + d = 2) : a + b + c + d = 10  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp at *
      linarith
  | solve
    | norm_num at *
      linarith
  | solve
    | field_simp at *
      linarith
  | solve
    | ring_nf at h₁ h₂ h₃ h₄
      linarith
  | solve
    | simp at *
      nlinarith
  | solve
    | norm_num at *
      nlinarith
  | solve
    | field_simp at *
      nlinarith
  | solve
    | ring_nf at h₁ h₂ h₃ h₄
      nlinarith
example : (∀ (a b c d : ℝ) (h₁ : a*0^3 + b*0^2 + c*0 + d = 4) (h₂ : a*1^3 + b*1^2 + c*1 + d = 10) (h₃ : a*2^3 + b*2^2 + c*2 + d = 26) (h₄ : a*(-1)^3 + b*(-1)^2 + c*(-1) + d = 2), a + b + c + d = 10) := @solution
#print axioms solution
