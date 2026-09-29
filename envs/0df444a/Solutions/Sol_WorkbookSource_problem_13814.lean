-- Prove2me | solution 1 for WorkbookSource.problem_13814
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:29.117015+00:00
-- url     : https://prove2.me/submissions/fdb91d1d-ca21-44b9-b3fb-4383174ced0a

/- InternLM Lean-Workbook, lean_workbook_13814, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b c d m n : ℝ)
  (h₀ : m = (a + b + c + d) / 4)
  (h₁ : n = (a + 3 + b + 3 + c + 3 + d + 3) / 4)
  (h₂ : abs (a - m) + abs (b - m) + abs (c - m) + abs (d - m) = 24) :
  abs (a + 3 - n) + abs (b + 3 - n) + abs (c + 3 - n) + abs (d + 3 - n) = 24  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | substs h₀ h₁
      ring_nf at h₂ ⊢
      linarith
  | solve
    | substs h₀ h₁
      ring_nf at h₂ ⊢
      nlinarith
example : (∀ (a b c d m n : ℝ)
  (h₀ : m = (a + b + c + d) / 4)
  (h₁ : n = (a + 3 + b + 3 + c + 3 + d + 3) / 4)
  (h₂ : abs (a - m) + abs (b - m) + abs (c - m) + abs (d - m) = 24), abs (a + 3 - n) + abs (b + 3 - n) + abs (c + 3 - n) + abs (d + 3 - n) = 24) := @solution
#print axioms solution
