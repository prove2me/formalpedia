-- Prove2me | solution 1 for WorkbookCorrected.plus_63663
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:57:53.740526+00:00
-- url     : https://prove2.me/submissions/2e56cd26-3309-4ef8-af2d-3f467372b0e0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (h : 1/(a+9*b)+1/(b+9*a)=5/24) : a*b ≤ 1 := by
  have h1 : a+9*b ≠ 0 := by positivity
  have h2 : b+9*a ≠ 0 := by positivity
  have he : 9*(a+b)^2+64*a*b=48*(a+b) := by
    field_simp [h1,h2] at h
    nlinarith only [h]
  nlinarith only [he,sq_nonneg (3*(a+b)-8)]
example : (∀ (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (h : 1/(a+9*b)+1/(b+9*a)=5/24), a*b ≤ 1) := @solution
#print axioms solution
