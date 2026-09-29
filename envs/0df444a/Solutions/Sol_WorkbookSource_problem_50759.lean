-- Prove2me | solution 1 for WorkbookSource.problem_50759
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:37:51.676248+00:00
-- url     : https://prove2.me/submissions/e8687435-ed52-499a-893d-bd1638a89419

/- Source: InternLM Lean-Workbook lean_workbook_50759, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
theorem solution :
  Finset.card (Finset.filter (λ x => Even x) (Finset.range 117)) = 59 := by
  decide

example : (Finset.card (Finset.filter (λ x => Even x) (Finset.range 117)) = 59) := @solution
#print axioms solution
