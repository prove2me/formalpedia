-- Prove2me | solution 1 for WorkbookSource.plus_525
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:05.640846+00:00
-- url     : https://prove2.me/submissions/70e775f4-23e7-42b2-ab04-f375a561a72f

/- Source: InternLM Lean-Workbook lean_workbook_plus_525, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 1 / (a + b + c) + 1 / (b + c) = 1 / c) :
  c^2 = a * b + b^2 := by
  have hc : c≠0 := ne_of_gt h₀.2.2
  have hs : b+c≠0 := ne_of_gt (add_pos h₀.2.1 h₀.2.2)
  have ht : a+b+c≠0 := ne_of_gt (add_pos (add_pos h₀.1 h₀.2.1) h₀.2.2)
  field_simp [hc,hs,ht] at h₁
  nlinarith [h₁]

example : (∀ (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 1 / (a + b + c) + 1 / (b + c) = 1 / c), c^2 = a * b + b^2) := @solution
#print axioms solution
