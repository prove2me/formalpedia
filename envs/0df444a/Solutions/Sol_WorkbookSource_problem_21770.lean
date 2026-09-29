-- Prove2me | solution 1 for WorkbookSource.problem_21770
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:03.23844+00:00
-- url     : https://prove2.me/submissions/7a24007e-c422-4957-b1b7-bde2129bca3e

/- InternLM Lean-Workbook, lean_workbook_21770, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (n : ℕ) (a : ℕ → ℝ) (b : ℕ → ℝ) (h₀ : 5 * a (n + 2) - 2 * a (n + 1) = b (n + 1))  (h₁ : 5 * a (n + 1) - 2 * a n = b n) (h₂ : b (n + 1) = 3 / 5 * b n + 2 / 5 * a (n + 1)) : 5 * a (n + 2) - 27 / 5 * a (n + 1) + 6 / 5 * a n = 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | revert h₀ h₁ h₂
      intros
      linarith
  | solve
    | have h₃ := h₀
      have h₄ := h₁
      linarith [h₀, h₁, h₂, h₃, h₄]
  | solve
    | revert h₀ h₁ h₂
      intros
      nlinarith
  | solve
    | have h₃ := h₀
      have h₄ := h₁
      nlinarith [h₀, h₁, h₂, h₃, h₄]
example : (∀ (n : ℕ) (a : ℕ → ℝ) (b : ℕ → ℝ) (h₀ : 5 * a (n + 2) - 2 * a (n + 1) = b (n + 1))  (h₁ : 5 * a (n + 1) - 2 * a n = b n) (h₂ : b (n + 1) = 3 / 5 * b n + 2 / 5 * a (n + 1)), 5 * a (n + 2) - 27 / 5 * a (n + 1) + 6 / 5 * a n = 0) := @solution
#print axioms solution
