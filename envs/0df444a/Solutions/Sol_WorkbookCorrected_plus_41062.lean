-- Prove2me | solution 1 for WorkbookCorrected.plus_41062
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:06:08.385679+00:00
-- url     : https://prove2.me/submissions/55cc0c93-e602-4873-8e33-cb79b7c092ee

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma gap (a : ℝ) (ha : 1≤a) : 0≤a-1/a := by
  have hp : 0<a := by linarith
  have hi : 1/a ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  linarith only [ha,hi]
private lemma cap (a : ℝ) (ha : 1≤a) (hg : a-1/a ≤ 6) :
    a^2 ≤ 1+(3+Real.sqrt 10)*(a-1/a) := by
  have hp : 0<a := by linarith
  have he : a*(a-1/a)=a^2-1 := by field_simp <;> ring
  have hm := mul_le_mul_of_nonneg_left hg (le_of_lt hp)
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  have hsp : 0<Real.sqrt 10 := by positivity
  have hb : a≤3+Real.sqrt 10 := by nlinarith only [hm,he,hs,hsp]
  have hh := mul_le_mul_of_nonneg_right hb (gap a ha)
  nlinarith only [he,hh]
theorem solution (a b c : ℝ) (ha : 1≤a) (hb : 1≤b) (hc : 1≤c)
    (h : a+b+c=1/a+1/b+1/c+6) : a^2+b^2+c^2 ≤ 21+6*Real.sqrt 10 := by
  have ga := gap a ha
  have gb := gap b hb
  have gc := gap c hc
  have ca := cap a ha (by linarith only [h,gb,gc])
  have cb := cap b hb (by linarith only [h,ga,gc])
  have cc := cap c hc (by linarith only [h,ga,gb])
  have hh := congrArg (fun x : ℝ => (3+Real.sqrt 10)*x) h
  nlinarith only [ca,cb,cc,hh]
example : (∀ (a b c : ℝ) (ha : 1≤a) (hb : 1≤b) (hc : 1≤c)
    (h : a+b+c=1/a+1/b+1/c+6), a^2+b^2+c^2 ≤ 21+6*Real.sqrt 10) := @solution
#print axioms solution
