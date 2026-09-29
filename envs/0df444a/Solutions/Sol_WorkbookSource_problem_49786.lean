-- Prove2me | solution 1 for WorkbookSource.problem_49786
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:55.744972+00:00
-- url     : https://prove2.me/submissions/44930d98-1f8b-4117-8e95-e599e433c46d

/- InternLM Lean-Workbook, lean_workbook_49786, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) :
  (a + b + c) ^ 3 - (a * (a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2) + b * (b ^ 2 + 3 * c ^ 2 + 3 * a ^ 2) + c * (c ^ 2 + 3 * a ^ 2 + 3 * b ^ 2)) ≥ 0 ↔ 6 * a * b * c ≥ 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor <;> intro h <;> linarith
  | solve
    | constructor <;> intro h
      ring_nf at h
      linarith
      ring_nf
      nlinarith
  | solve
    | constructor
      intro h
      ring_nf at h
      linarith
      intro h
      ring_nf
      nlinarith
  | solve
    | field_simp [mul_assoc]
      ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | constructor <;> intro h <;> nlinarith
  | solve
    | field_simp [mul_assoc]
      ring_nf
      constructor <;> intro h <;> nlinarith
example : (∀ (a b c : ℝ), (a + b + c) ^ 3 - (a * (a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2) + b * (b ^ 2 + 3 * c ^ 2 + 3 * a ^ 2) + c * (c ^ 2 + 3 * a ^ 2 + 3 * b ^ 2)) ≥ 0 ↔ 6 * a * b * c ≥ 0) := @solution
#print axioms solution
