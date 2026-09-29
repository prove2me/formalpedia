-- Prove2me | solution 1 for WorkbookSource.problem_24835
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:31.775879+00:00
-- url     : https://prove2.me/submissions/1caa1fa3-8db2-4ddd-82eb-a9b061339166

/- Source: InternLM Lean-Workbook lean_workbook_24835, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution  (q e : ℕ)
  (h₀ : q = 123456789 * 987654321)
  (h₁ : e = 121932631112635269) :
  q = e := by
  norm_num [h₀, h₁]

example : (∀ (q e : ℕ)
  (h₀ : q = 123456789 * 987654321)
  (h₁ : e = 121932631112635269), q = e) := @solution
#print axioms solution
