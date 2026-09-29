-- Prove2me | solution 1 for WorkbookSource.plus_68505
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:26:42.184385+00:00
-- url     : https://prove2.me/submissions/4f2b879b-c756-4f2d-bbdf-cd6119119f0a

/- InternLM Lean-Workbook, lean_workbook_plus_68505, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (hf: f = fun x => x / (1 - x)) : ¬ (f ∘ f) = f   := by
  intro he
  have h := congrFun he (1/4)
  norm_num [hf,Function.comp_apply] at h

example : (∀ (f : ℝ → ℝ) (hf: f = fun x => x / (1 - x)), ¬ (f ∘ f) = f) := @solution
#print axioms solution
