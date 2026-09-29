-- Prove2me | solution 1 for WorkbookSource.plus_8564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:10:21.611521+00:00
-- url     : https://prove2.me/submissions/7b85ea7f-2258-4097-8e54-192b7ae734f9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a : ℕ → ℝ) (a0 : a 0 = 1/3)
    (h : ∀ n, a (n+1)=Real.sqrt ((1+a n)/2)) : ∀ n, a n ≤ a (n+1) := by
  intro n
  induction n with
  | zero =>
    rw [h 0,a0]
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ (1+1/3)/2 by norm_num)
    have hp := Real.sqrt_nonneg ((1+1/3)/2)
    nlinarith only [hs,hp]
  | succ n ih =>
    rw [h (n+1),h n]
    rw [h n] at ih
    apply Real.sqrt_le_sqrt
    linarith only [ih]
example : (∀ (a : ℕ → ℝ) (a0 : a 0 = 1/3)
    (h : ∀ n, a (n+1)=Real.sqrt ((1+a n)/2)), ∀ n, a n ≤ a (n+1)) := @solution
#print axioms solution
