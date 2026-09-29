-- Prove2me | solution 1 for WorkbookCorrected.plus_18160
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:21:05.598439+00:00
-- url     : https://prove2.me/submissions/f83ecb95-0897-4645-a855-f5335a814ff3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : u^3=1+a) (hv : v^3=1+2*b) (h : u+v=3) :
    159/2-54*Real.sqrt 2 ≤ a+b ∧ a+b ≤ 7 := by
  have hmono : StrictMono (fun t : ℝ => t^3) := Odd.strictMono_pow (by decide : Odd 3)
  have hu1 : 1 ≤ u := hmono.le_iff_le.mp (by nlinarith only [hu,ha])
  have hv1 : 1 ≤ v := hmono.le_iff_le.mp (by nlinarith only [hv,hb])
  have hu2 : u ≤ 2 := by linarith only [h,hv1]
  have he : v=3-u := by linarith only [h]
  rw [he] at hv
  have hid : 2*(a+b)=u^3+9*u^2-27*u+24 := by nlinarith only [hu,hv]
  constructor
  · have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    have hs3 : (Real.sqrt 2)^3=2*Real.sqrt 2 := by rw [pow_succ,hs]
    have hsu := congrArg (fun t : ℝ => u*t) hs
    have hi : 2*(a+b-(159/2-54*Real.sqrt 2)) =
        (u+3+6*Real.sqrt 2)*(u+3-3*Real.sqrt 2)^2 := by
      nlinarith only [hid,hs,hs3,hsu]
    have hp : 0 ≤ (u+3+6*Real.sqrt 2)*(u+3-3*Real.sqrt 2)^2 := by
      apply mul_nonneg
      · nlinarith only [hu1,Real.sqrt_nonneg 2]
      · exact sq_nonneg _
    linarith only [hi,hp]
  · have hq : 0 ≤ u^2+11*u-5 := by nlinarith only [hu1,sq_nonneg u]
    have hp := mul_nonneg (sub_nonneg.mpr hu2) hq
    nlinarith only [hid,hp]
example : (∀ (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : u^3=1+a) (hv : v^3=1+2*b) (h : u+v=3),
    159/2-54*Real.sqrt 2 ≤ a+b ∧ a+b ≤ 7) := @solution
#print axioms solution
