-- Prove2me | solution 1 for WorkbookCorrected.plus_21177
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:12:54.526972+00:00
-- url     : https://prove2.me/submissions/19cf8ad4-0d75-4397-a63a-7d6a363157db

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution :
    (∀ x y : ℝ, (x+1)*(y+1)=9 → 8 ≤ x^2+y^2) ∧
    (∃ x y : ℝ, (x+1)*(y+1)=9 ∧ x^2+y^2=8) := by
  constructor
  · intro x y h
    nlinarith only [h,sq_nonneg (x+y-4),sq_nonneg (x-y)]
  · exact ⟨2,2,by norm_num,by norm_num⟩
example : ((∀ x y : ℝ, (x+1)*(y+1)=9 → 8 ≤ x^2+y^2) ∧
    (∃ x y : ℝ, (x+1)*(y+1)=9 ∧ x^2+y^2=8)) := @solution
#print axioms solution
