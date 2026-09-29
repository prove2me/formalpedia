-- Prove2me | solution 1 for WorkbookSource.problem_34736
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:28.367225+00:00
-- url     : https://prove2.me/submissions/3d3da50d-8d3e-4c81-8b8b-a2e5e310dd6b

/- Source: InternLM Lean-Workbook, record lean_workbook_34736.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x + 2 * f (27 - x) = x) : f 11 = 7 := by
  first
  | solve
    | have h1 := hf 11
      have h2 := hf (27 - 11)
      simp at h2
      linarith
  | solve
    | have h₁ := hf 11
      have h₂ := hf (27 - 11)
      simp at h₂
      linarith
  | solve
    | have h₁ := hf 11
      have h₂ := hf (27 - 11)
      norm_num at *
      linarith
  | solve
    | have h1 := hf 11
      have h2 := hf (27 - 11)
      simp at h1 h2
      linarith
  | solve
    | have h1 := hf 11
      have h2 := hf (27 - 11)
      norm_num at *
      linarith
  | solve
    | have h1 := hf 11
      have h2 := hf (27-11)
      norm_num at h1 h2
      linarith

example : (∀ (f : ℝ → ℝ) (hf : ∀ x, f x + 2 * f (27 - x) = x), f 11 = 7) := @solution
#print axioms solution
