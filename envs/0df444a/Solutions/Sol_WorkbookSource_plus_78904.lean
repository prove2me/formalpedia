-- Prove2me | solution 1 for WorkbookSource.plus_78904
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:12:46.00791+00:00
-- url     : https://prove2.me/submissions/ee437a46-4e5d-42c5-818f-fdc11deccd00

/- InternLM Lean-Workbook, lean_workbook_plus_78904, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 2 ^ 100 ≡ 1 [ZMOD 125] ∧ 2 ^ 100 ≡ 0 [ZMOD 8] → 2 ^ 100 ≡ 376 [ZMOD 1000]   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [Int.ModEq]
  | solve
    | simp only [Int.ModEq]
      omega
  | solve
    | simp only [Int.ModEq]
      norm_num
  | solve
    | intro h
      rw [Int.ModEq] at *
      omega
example : (2 ^ 100 ≡ 1 [ZMOD 125] ∧ 2 ^ 100 ≡ 0 [ZMOD 8] → 2 ^ 100 ≡ 376 [ZMOD 1000]) := @solution
#print axioms solution
