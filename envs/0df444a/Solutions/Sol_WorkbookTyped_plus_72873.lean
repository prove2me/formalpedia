-- Prove2me | solution 1 for WorkbookTyped.plus_72873
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:38.532209+00:00
-- url     : https://prove2.me/submissions/ac3cf1e1-0c55-48f2-9e07-42c6a69442ac

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_72873, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Explicit-binder repair: the original declaration omits t. Here t is declared real,
as its source condition t∈(0,1) requires. No natural-number interpretation is used. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem solution (x y t : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 0 < t ∧ t < 1) :
    (x + y)^t ≤ x^t + y^t := by
  exact Real.rpow_add_le_add_rpow hx.le hy.le h.1.le h.2.le

example : (∀ (x y t : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 0 < t ∧ t < 1),
    (x + y)^t ≤ x^t + y^t) := @solution
#print axioms solution
