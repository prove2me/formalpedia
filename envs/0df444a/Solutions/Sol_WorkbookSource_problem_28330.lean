-- Prove2me | solution 1 for WorkbookSource.problem_28330
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:22.956171+00:00
-- url     : https://prove2.me/submissions/26c941a4-cdad-4c75-b323-19978f92b960

/- Source: InternLM Lean-Workbook, record lean_workbook_28330.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 + 2 * x * y * z = 1) : (x * y / (x * y + z) + y * z / (y * z + x) + z * x / (z * x + y) = 1 ↔ x / (x + y * z) + y / (y + z * x) + z / (z + x * y) = 2) := by
  first
  | solve
    | field_simp [add_comm]
      ring_nf at h ⊢
      constructor <;> intro h' <;> linarith
  | solve
    | field_simp [h]
      ring_nf
      constructor <;> intro h <;> linarith [h, hx, hy, hz, h]

example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 + 2 * x * y * z = 1), (x * y / (x * y + z) + y * z / (y * z + x) + z * x / (z * x + y) = 1 ↔ x / (x + y * z) + y / (y + z * x) + z / (z + x * y) = 2)) := @solution
#print axioms solution
