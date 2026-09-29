-- Prove2me | solution 1 for WorkbookSource.problem_53725
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:42.988946+00:00
-- url     : https://prove2.me/submissions/745c435e-61df-4c11-ad4e-3237f3d511ec

/- Source: InternLM Lean-Workbook, record lean_workbook_53725.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (n : ℝ) (h : n > 25 / 12) : Real.sqrt (n * (n + 2)) > n + 5 / 6 := by
  first
  | solve
    | apply Real.lt_sqrt_of_sq_lt
      nlinarith
  | solve
    | apply Real.lt_sqrt_of_sq_lt
      ring_nf
      norm_num
      nlinarith
  | solve
    | apply Real.lt_sqrt_of_sq_lt
      field_simp
      ring_nf
      norm_num
      nlinarith
  | solve
    | have h1 : 0 < n := by positivity
      apply Real.lt_sqrt_of_sq_lt
      nlinarith [h, h1]
  | solve
    | have : n * (n + 2) > (n + 5 / 6) ^ 2 := by nlinarith
      exact Real.lt_sqrt_of_sq_lt this

example : (∀ (n : ℝ) (h : n > 25 / 12), Real.sqrt (n * (n + 2)) > n + 5 / 6) := @solution
#print axioms solution
