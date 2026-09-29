-- Prove2me | solution 1 for WorkbookCorrected.plus_61420
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:57:51.881301+00:00
-- url     : https://prove2.me/submissions/9f43645e-6444-4122-92ba-91899704fd23

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (hxy : x*y+y*z+z*x=1)
    (h : 1/(1+x^2)+1/(1+y^2)=5/(1+z^2)) : z=2*(x+y) := by
  have he : 1-x*y=z*(x+y) := by nlinarith only [hxy]
  have hi : (1+x^2)*(1+y^2)=(x+y)^2*(1+z^2) := by
    calc
      (1+x^2)*(1+y^2)=(x+y)^2+(1-x*y)^2 := by ring
      _=(x+y)^2*(1+z^2) := by rw [he]; ring
  have hg : (2+x^2+y^2)*(1+z^2)=5*(1+x^2)*(1+y^2) := by
    field_simp at h
    nlinarith only [h]
  have hk : (2+x^2+y^2)*(1+z^2)=(5*(x+y)^2)*(1+z^2) := by
    rw [mul_assoc, ← hi]
    nlinarith only [hg]
  have hn : 1+z^2 ≠ 0 := by positivity
  have hc := mul_right_cancel₀ hn hk
  have hs : 0 < x+y := by linarith
  have hf : (z-2*(x+y))*(x+y)=0 := by nlinarith only [hc,hxy]
  have hh := (mul_eq_zero.mp hf).resolve_right (ne_of_gt hs)
  linarith only [hh]
example : (∀ (x y z : ℝ) (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (hxy : x*y+y*z+z*x=1)
    (h : 1/(1+x^2)+1/(1+y^2)=5/(1+z^2)), z=2*(x+y)) := @solution
#print axioms solution
