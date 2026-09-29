-- Prove2me | solution 1 for WorkbookCorrected.plus_32112
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:44:28.276592+00:00
-- url     : https://prove2.me/submissions/802f995f-9915-49a6-9f2a-fccf5b09bb9f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma ordered (x y z : ℝ) (hz : 0 ≤ z) (hxy : y ≤ x) (hyz : z ≤ y) :
    0 ≤ (x+y+z)^3+9*x*y*z-4*(x+y+z)*(x*y+y*z+z*x) := by
  have h1 := mul_nonneg (sq_nonneg (x-y)) (show 0 ≤ x+y-z by linarith)
  have h2 := mul_nonneg (mul_nonneg hz (sub_nonneg.mpr (le_trans hyz hxy))) (sub_nonneg.mpr hyz)
  nlinarith only [h1,h2]
private lemma schur (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x+y+z)^3 ≤ 2*(x+y+z)*(x^2+y^2+z^2)+9*x*y*z := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · nlinarith only [ordered z y x hx hyz hxy]
    · rcases le_total x z with hxz | hzx
      · nlinarith only [ordered y z x hx hzy hxz]
      · nlinarith only [ordered y x z hz hxy hzx]
  · rcases le_total x z with hxz | hzx
    · nlinarith only [ordered z x y hy hxz hyx]
    · rcases le_total y z with hyz | hzy
      · nlinarith only [ordered x z y hy hzx hyz]
      · nlinarith only [ordered x y z hz hyx hzy]
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^4+b^4+c^4+a*b*c=4) : a^2+b^2+c^2 ≤ 3 := by
  let s := a^2+b^2+c^2
  let r := a*b*c
  let t := a^4+b^4+c^4
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : t+r=4 := h
  have hs2 : s^2 ≤ 3*t := by
    dsimp [s,t]
    nlinarith only [sq_nonneg (a^2-b^2),sq_nonneg (b^2-c^2),sq_nonneg (c^2-a^2)]
  have hsch : s^3 ≤ 2*s*t+9*r^2 := by
    dsimp [s,t,r]
    nlinarith only [schur (a^2) (b^2) (c^2) (sq_nonneg a) (sq_nonneg b) (sq_nonneg c)]
  change s ≤ 3
  by_contra hn
  have hs : 3 < s := by linarith only [hn]
  have hr1 : r < 1 := by nlinarith only [hs2,ht,hs,sq_nonneg (s-3)]
  have hp := mul_nonneg (show 0 ≤ 1-r by linarith) (show 0 ≤ 3*r+1 by linarith)
  have hs3 : 9*s < s^3 := by
    have hh : 9 < s^2 := by nlinarith only [hs,sq_nonneg (s-3)]
    have hh2 := mul_lt_mul_of_pos_right hh (show 0<s by linarith)
    nlinarith only [hh2]
  have hm := mul_nonneg (show 0 ≤ s-3 by linarith) (show 0 ≤ 1+2*r by linarith)
  have he := congrArg (fun v : ℝ => s*v) ht
  nlinarith only [hsch,he,hs3,hm,hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^4+b^4+c^4+a*b*c=4), a^2+b^2+c^2 ≤ 3) := @solution
#print axioms solution
