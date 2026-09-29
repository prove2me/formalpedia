-- Prove2me | solution 1 for WorkbookSource.problem_13207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:24.981979+00:00
-- url     : https://prove2.me/submissions/3a02a239-4c3c-4835-9619-a04b067e884f

/- InternLM Lean-Workbook, lean_workbook_13207, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b c d e f : ℝ)
  (h₀ : a^2 + b^2 + e^2 + a * b * e = 4)
  (h₁ : f^2 + c^2 + d^2 + f * c * d = 4) :
  a^2 + b^2 + c^2 + d^2 + e^2 + f^2 + a * b * e + f * c * d = 8  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [h₁, h₀]
  | solve
    | ring_nf at *
      linarith
  | solve
    | simp only [sq]
      linarith
  | solve
    | nlinarith only [h₀, h₁]
  | solve
    | nlinarith [h₁, h₀]
  | solve
    | ring_nf at *
      nlinarith
  | solve
    | simp only [sq]
      nlinarith
example : (∀ (a b c d e f : ℝ)
  (h₀ : a^2 + b^2 + e^2 + a * b * e = 4)
  (h₁ : f^2 + c^2 + d^2 + f * c * d = 4), a^2 + b^2 + c^2 + d^2 + e^2 + f^2 + a * b * e + f * c * d = 8) := @solution
#print axioms solution
