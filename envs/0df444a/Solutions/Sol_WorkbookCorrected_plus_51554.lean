-- Prove2me | solution 1 for WorkbookCorrected.plus_51554
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:18:04.873287+00:00
-- url     : https://prove2.me/submissions/4a9232b5-b491-4f30-84d6-5e2bcfc932bd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x : ℝ) :
    (∃ a b : ℝ, a^3=20+x*Real.sqrt 2 ∧ b^3=20-x*Real.sqrt 2 ∧ a+b=4) ↔
    (x=14 ∨ x= -14) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    have hp : a*b=2 := by
      have he : a=4-b := by linarith only [hab]
      rw [he] at ha ⊢
      nlinarith only [ha,hb]
    have hi : (a*b)^3=(20+x*Real.sqrt 2)*(20-x*Real.sqrt 2) := by
      rw [mul_pow,ha,hb]
    rw [hp] at hi
    have hxs : (x*Real.sqrt 2)^2=2*x^2 := by rw [mul_pow,hs]; ring
    have hf : (x-14)*(x+14)=0 := by nlinarith only [hi,hxs]
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl (by linarith only [h])
    · exact Or.inr (by linarith only [h])
  · have hs3 : (Real.sqrt 2)^3=2*Real.sqrt 2 := by rw [pow_succ,hs]
    rintro (rfl | rfl)
    · refine ⟨2+Real.sqrt 2,2-Real.sqrt 2,?_,?_,?_⟩ <;> nlinarith only [hs,hs3]
    · refine ⟨2-Real.sqrt 2,2+Real.sqrt 2,?_,?_,?_⟩ <;> nlinarith only [hs,hs3]
example : (∀ (x : ℝ),
    (∃ a b : ℝ, a^3=20+x*Real.sqrt 2 ∧ b^3=20-x*Real.sqrt 2 ∧ a+b=4) ↔
    (x=14 ∨ x= -14)) := @solution
#print axioms solution
