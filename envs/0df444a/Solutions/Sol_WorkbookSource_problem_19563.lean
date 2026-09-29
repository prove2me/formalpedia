-- Prove2me | solution 1 for WorkbookSource.problem_19563
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:14.330811+00:00
-- url     : https://prove2.me/submissions/587142bf-6fab-4de4-899b-d6046b82dc68

/- InternLM Lean-Workbook, lean_workbook_19563, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (n : ℕ) (hn : n ≠ 0) : (n : ℝ) / (n + 1) - (n : ℝ) / ((n + 1) * n ^ n) = (n * (n ^ n - 1)) / (n ^ n * (n + 1))  := by
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnn]

example : (∀ (n : ℕ) (hn : n ≠ 0), (n : ℝ) / (n + 1) - (n : ℝ) / ((n + 1) * n ^ n) = (n * (n ^ n - 1)) / (n ^ n * (n + 1))) := @solution
#print axioms solution
