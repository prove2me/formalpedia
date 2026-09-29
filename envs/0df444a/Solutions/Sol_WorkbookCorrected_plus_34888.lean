-- Prove2me | solution 1 for WorkbookCorrected.plus_34888
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:57:03.150092+00:00
-- url     : https://prove2.me/submissions/539fb7da-27d0-445b-892e-9f5bdbb53593

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
private lemma root_recurrence (r : ℝ) (hr : r^2=4*r+1) (n : ℕ) :
    r^(n+2)=4*r^(n+1)+r^n := by
  rw [pow_add,hr,pow_succ]
  ring

theorem solution (a : ℕ → ℝ) (h0 : a 0=1) (h1 : a 1=2)
    (h : ∀ n : ℕ, a (n+2)=4*a (n+1)+a n) :
    ∀ n : ℕ, a n=((2+Real.sqrt 5)^n+(2-Real.sqrt 5)^n)/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hr : (2+Real.sqrt 5)^2=4*(2+Real.sqrt 5)+1 := by nlinarith only [hs]
  have ht : (2-Real.sqrt 5)^2=4*(2-Real.sqrt 5)+1 := by nlinarith only [hs]
  have hf : ∀ n : ℕ,
      a n=((2+Real.sqrt 5)^n+(2-Real.sqrt 5)^n)/2 ∧
      a (n+1)=((2+Real.sqrt 5)^(n+1)+(2-Real.sqrt 5)^(n+1))/2 := by
    intro n
    induction n with
    | zero => norm_num [h0,h1]
    | succ n ih =>
      refine ⟨ih.2,?_⟩
      rw [show n+1+1=n+2 by omega, h n, ih.1, ih.2,
        root_recurrence _ hr n, root_recurrence _ ht n]
      ring
  intro n
  exact (hf n).1
example : (∀ (a : ℕ → ℝ) (h0 : a 0=1) (h1 : a 1=2)
    (h : ∀ n : ℕ, a (n+2)=4*a (n+1)+a n),
    ∀ n : ℕ, a n=((2+Real.sqrt 5)^n+(2-Real.sqrt 5)^n)/2) := @solution
#print axioms solution
