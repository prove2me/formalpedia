-- Prove2me | solution 1 for WorkbookSource.problem_39600
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:49.880618+00:00
-- url     : https://prove2.me/submissions/fdfc8a9d-ad22-4fa6-9484-93ea81b2d5be

/- InternLM Lean-Workbook, lean_workbook_39600, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (y : ℕ → ℝ) (n : ℕ) (h₁ : y 0 = 3/2) (h₂ : ∀ n, y (n+1) = (y n)/2) : y n = 3 / 2 ^ (n + 1)  := by
  first
  | solve
    | induction n with
      | zero => norm_num [h₁]
      | succ n ih => rw [h₂,ih]; simp [pow_succ]; ring
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | induction' n with n ih
      simp [h₁]
      simp [h₂, ih, pow_succ]
      ring
  | solve
    | induction' n with n ih
      simp [h₁]
      simp [ih, h₂, pow_succ]
      ring
  | solve
    | induction' n with n hn
      simp [h₁]
      rw [h₂, hn]
      simp [pow_succ]
      ring
  | solve
    | induction' n with n ih
      simp [h₁, h₂]
      simp [h₂, ih, pow_succ]
      ring
example : (∀ (y : ℕ → ℝ) (n : ℕ) (h₁ : y 0 = 3/2) (h₂ : ∀ n, y (n+1) = (y n)/2), y n = 3 / 2 ^ (n + 1)) := @solution
#print axioms solution
