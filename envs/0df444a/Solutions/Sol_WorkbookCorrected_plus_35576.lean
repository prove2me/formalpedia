-- Prove2me | solution 1 for WorkbookCorrected.plus_35576
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:33:04.189651+00:00
-- url     : https://prove2.me/submissions/8c799d45-fa9f-49e3-8e6e-511a26156cea

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (h : 1/(a^2+2)+1/(b^2+2)=(1/3 : ℝ)) : 1/a+1/b ≥ 1 := by
  have he : (a*b)^2=a^2+b^2+8 := by
    field_simp at h
    nlinarith only [h]
  have hp0 := mul_pos ha hb
  have hp : 4 ≤ a*b := by
    by_contra hn
    have hn' : a*b-4<0 := by linarith only [hn]
    have ht : 0 < a*b+2 := by linarith only [hp0]
    have hh := mul_neg_of_neg_of_pos hn' ht
    nlinarith only [he,hh,sq_nonneg (a-b)]
  have hs : a*b ≤ a+b := by
    by_contra hn
    have hn' : a+b-a*b<0 := by linarith only [hn]
    have ht : 0 < a+b+a*b := by positivity
    have hh := mul_neg_of_neg_of_pos hn' ht
    nlinarith only [he,hp,hh]
  have hid : 1/a+1/b=(a+b)/(a*b) := by field_simp; ring
  rw [hid]
  exact (le_div_iff₀ hp0).2 (by linarith only [hs])
example : (∀ (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (h : 1/(a^2+2)+1/(b^2+2)=(1/3 : ℝ)), 1/a+1/b ≥ 1) := @solution
#print axioms solution
