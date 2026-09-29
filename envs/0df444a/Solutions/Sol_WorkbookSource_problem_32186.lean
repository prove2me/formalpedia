-- Prove2me | solution 1 for WorkbookSource.problem_32186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:25.975149+00:00
-- url     : https://prove2.me/submissions/7bc1cb50-fa74-4299-8d36-43b92feabaa6

/- Source: InternLM Lean-Workbook, record lean_workbook_32186.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (f : ℝ → ℝ) (hf1 : f 0 = 0) (hf2 : f 1 = 1) (hf3 : ∀ x ≠ 0, f (x^2 + 1/x) = (f x)^2 + f (1/x)) : f 2 = 2 := by
  first
  | solve
    | have h0 := hf3 1 (by norm_num)
      simp [hf1, hf2] at h0
      norm_num at h0
      exact h0
  | solve
    | have h1 := hf3 1 (by norm_num)
      simp [hf1, hf2] at h1
      norm_num at h1
      exact h1
  | solve
    | have h2 := hf3 1 (by norm_num)
      simp [hf1, hf2] at h2
      norm_num at h2
      exact h2
  | solve
    | have h1 := hf3 1 (by norm_num)
      simp [hf1, hf2] at h1
      norm_num at h1
      linarith
  | solve
    | have := hf3 1 (by norm_num)
      simp [hf1, hf2] at this
      norm_num at this
      exact this
  | solve
    | have h1 := hf3 1 (by norm_num)
      simp [hf1, hf2, h1] at h1
      norm_num at h1
      exact h1

example : (∀ (f : ℝ → ℝ) (hf1 : f 0 = 0) (hf2 : f 1 = 1) (hf3 : ∀ x ≠ 0, f (x^2 + 1/x) = (f x)^2 + f (1/x)), f 2 = 2) := @solution
#print axioms solution
