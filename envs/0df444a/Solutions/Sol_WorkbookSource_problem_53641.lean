-- Prove2me | solution 1 for WorkbookSource.problem_53641
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:57.398443+00:00
-- url     : https://prove2.me/submissions/92d13526-d2eb-47d3-b2fb-010addbeaf33

/- Source: InternLM Lean-Workbook lean_workbook_53641, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution :
  (5^400) % 19 = 17 := by
  norm_num

example : ((5^400) % 19 = 17) := @solution
#print axioms solution
