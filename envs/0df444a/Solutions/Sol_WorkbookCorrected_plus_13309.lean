-- Prove2me | solution 1 for WorkbookCorrected.plus_13309
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:12:55.41425+00:00
-- url     : https://prove2.me/submissions/5cecd30b-e7eb-4268-94c4-2668c98cc237

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution :
    (∀ x y : ℝ, 4*x^2+9*y^2=36 → x^2+(2/3)*x*y+(3/2)*y^2 ≤ 10) ∧
    (∃ x y : ℝ, 4*x^2+9*y^2=36 ∧ x^2+(2/3)*x*y+(3/2)*y^2=10) := by
  constructor
  · intro x y h
    nlinarith only [h,sq_nonneg (x-3*y)]
  · have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
    refine ⟨6*Real.sqrt 5/5,2*Real.sqrt 5/5,?_,?_⟩ <;> nlinarith only [hs]
example : ((∀ x y : ℝ, 4*x^2+9*y^2=36 → x^2+(2/3)*x*y+(3/2)*y^2 ≤ 10) ∧
    (∃ x y : ℝ, 4*x^2+9*y^2=36 ∧ x^2+(2/3)*x*y+(3/2)*y^2=10)) := @solution
#print axioms solution
