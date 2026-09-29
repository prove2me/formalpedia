-- Prove2me | solution 1 for WorkbookSource.problem_51655
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:01.387556+00:00
-- url     : https://prove2.me/submissions/eaf003d4-ceac-4bd0-8a9d-4301fbfa1207

/- InternLM Lean-Workbook, lean_workbook_51655, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (h₁ : 2 ∣ 2310) (h₂ : 3 ∣ 2310) (h₃ : 5 ∣ 2310) (h₄ : 7 ∣ 2310) (h₅ : 11 ∣ 2310) : 2310 = 2*3*5*7*11  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [h₁, h₂, h₃, h₄, h₅]
  | solve
    | simp [h₅, h₄, h₃, h₂, h₁]
  | solve
    | ring_nf at h₁ h₂ h₃ h₄ h₅ ⊢
  | solve
    | norm_num at h₁ h₂ h₃ h₄ h₅ ⊢
example : (∀ (h₁ : 2 ∣ 2310) (h₂ : 3 ∣ 2310) (h₃ : 5 ∣ 2310) (h₄ : 7 ∣ 2310) (h₅ : 11 ∣ 2310), 2310 = 2*3*5*7*11) := @solution
#print axioms solution
