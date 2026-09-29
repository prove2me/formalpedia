-- Prove2me | solution 1 for WorkbookSource.problem_18412
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:49.266634+00:00
-- url     : https://prove2.me/submissions/5da55072-25e7-43cc-96c0-25fe6774d5d9

/- Source: InternLM Lean-Workbook, record lean_workbook_18412.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (f : ℝ → ℝ) (a : ℝ) (h₁ : f = fun x => x^5 + x^3 + 1) (h₂ : f a = 7) : f (-a) = -5 := by
  first
  | solve
    | simp [h₁] at h₂ ⊢
      linarith
  | solve
    | simp [h₁, h₂] at *
      linarith
  | solve
    | simp [h₁] at h₂ ⊢
      linarith [h₂]
  | solve
    | simp only [h₁, h₂] at *
      linarith
  | solve
    | simp [h₁, h₂]
      simp [h₁] at h₂
      linarith
  | solve
    | simp [h₁, h₂]
      simp [h₁] at h₂
      nlinarith

example : (∀ (f : ℝ → ℝ) (a : ℝ) (h₁ : f = fun x => x^5 + x^3 + 1) (h₂ : f a = 7), f (-a) = -5) := @solution
#print axioms solution
