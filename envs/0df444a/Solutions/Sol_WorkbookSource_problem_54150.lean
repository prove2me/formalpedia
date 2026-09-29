-- Prove2me | solution 1 for WorkbookSource.problem_54150
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:58.878873+00:00
-- url     : https://prove2.me/submissions/665330d3-1c0e-4ccd-b3c5-e43c8b048fd2

/- Source: InternLM Lean-Workbook lean_workbook_54150, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution (a k : ℝ) (h : a ≠ -k) : (a^2 + 1) / (a + k) = a - k + (k^2 + 1) / (a + k) := by
  have hd : a+k≠0 := by intro he; apply h; linarith
  field_simp [hd]
  ring

example : (∀ (a k : ℝ) (h : a ≠ -k), (a^2 + 1) / (a + k) = a - k + (k^2 + 1) / (a + k)) := @solution
#print axioms solution
