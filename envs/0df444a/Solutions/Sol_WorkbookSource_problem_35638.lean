-- Prove2me | solution 1 for WorkbookSource.problem_35638
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:29.084256+00:00
-- url     : https://prove2.me/submissions/6b506471-e712-41e9-91d7-b8057f4a91bd

/- Source: InternLM Lean-Workbook, record lean_workbook_35638.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c: ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c): (a+b)^2+(b+c)^2+(c+a)^2=3 → 2*b*c+3*(b^2+c^2)<6 := by
  first
  | solve
    | ring_nf
      intro h
      norm_num at h ⊢
      nlinarith
  | solve
    | ring_nf
      intro h
      nlinarith [h, ha, hb, hc]

example : (∀ (a b c: ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a+b)^2+(b+c)^2+(c+a)^2=3 → 2*b*c+3*(b^2+c^2)<6) := @solution
#print axioms solution
