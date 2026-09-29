-- Prove2me | solution 1 for WorkbookSource.plus_63997
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:12:47.815983+00:00
-- url     : https://prove2.me/submissions/68af367a-4761-4dbe-9e8f-366106bac36d

/- InternLM Lean-Workbook, lean_workbook_plus_63997, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (hx : x > 2000) : x^2000 - x^1999 > 2000^2000 - 2000^1999   := by
  have fact (t : ℝ) : t^2000 - t^1999 = t^1999 * (t-1) := by
    rw [show 2000 = 1999 + 1 from rfl, pow_succ]
    ring
  rw [fact x, fact 2000]
  gcongr <;> norm_num

example : (∀ (x : ℝ) (hx : x > 2000), x^2000 - x^1999 > 2000^2000 - 2000^1999) := @solution
#print axioms solution
