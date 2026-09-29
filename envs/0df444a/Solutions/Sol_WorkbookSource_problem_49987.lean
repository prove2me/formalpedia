-- Prove2me | solution 1 for WorkbookSource.problem_49987
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:56.378425+00:00
-- url     : https://prove2.me/submissions/b409a91f-8a81-4322-a3b0-fe565b5d40e1

/- InternLM Lean-Workbook, lean_workbook_49987, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : 9 * Real.cos x - 12 * Real.cos x = -3 * Real.cos x  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf at x ⊢
  | solve
    | simp [mul_sub]
      ring
  | solve
    | rw [eq_comm]
      ring_nf
  | solve
    | simp [mul_comm]
      ring
example : (∀ (x : ℝ), 9 * Real.cos x - 12 * Real.cos x = -3 * Real.cos x) := @solution
#print axioms solution
