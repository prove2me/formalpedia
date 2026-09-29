-- Prove2me | solution 1 for WorkbookSource.base_31687
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:22:14.18962+00:00
-- url     : https://prove2.me/submissions/ea683d40-4493-4895-b60e-9e448261d12e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
private lemma box_polynomial_nonneg (p q x y : ℝ) (hp : 0<p) (hq : 0<q)
    (hx : 0<x) (hy : 0<y) (hX : 4*x≤p^2) (hY : 4*y≤q^2) :
    0 ≤ 4*(p+q)^2*(q*(p+q)+x)*(p*(p+q)+y)
      -81*p*q*((x-y)^2+(p+q)*(x*q+y*p)) := by
  have hu : 0≤p^2-4*x := sub_nonneg.mpr hX
  have hv : 0≤q^2-4*y := sub_nonneg.mpr hY
  have he : 16*p^2*q^2*(4*(p+q)^2*(q*(p+q)+x)*(p*(p+q)+y)
      -81*p*q*((x-y)^2+(p+q)*(x*q+y*p))) =
      16*x*y*((p-q)^2*(p+q)^2*(16*p^2+31*p*q+16*q^2))
      +4*y*(p^2-4*x)*(q*(2*p+q)^2*(16*p^3+12*q*(2*p-q)^2+15*p*q^2+4*q^3))
      +4*x*(q^2-4*y)*(p*(p+2*q)^2*(16*q^3+12*p*(2*q-p)^2+15*q*p^2+4*p^3))
      +(p^2-4*x)*(q^2-4*y)*(64*p*q*(p+q)^4)
      +324*p^3*q^3*(x*(p^2-4*x)+y*(q^2-4*y)) := by ring
  have hm : 0 ≤ 16*p^2*q^2*(4*(p+q)^2*(q*(p+q)+x)*(p*(p+q)+y)
      -81*p*q*((x-y)^2+(p+q)*(x*q+y*p))) := by
    rw [he]
    positivity
  exact nonneg_of_mul_nonneg_right hm (by positivity)

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / (c + a) + 1 / (b + d)) ≥ (81 / 4) * (a + b) * (b + c) * (c + d) * (d + a) / ((a + b + c + d) * (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d))   := by
  let p := a+c
  let q := b+d
  let x := a*c
  let y := b*d
  let E := (x-y)^2+(p+q)*(x*q+y*p)
  let H := (q*(p+q)+x)*(p*(p+q)+y)
  have hp : 0<p := by dsimp [p]; positivity
  have hq : 0<q := by dsimp [q]; positivity
  have hx : 0<x := by dsimp [x]; positivity
  have hy : 0<y := by dsimp [y]; positivity
  have hX : 4*x≤p^2 := by dsimp [p,x]; nlinarith only [sq_nonneg (a-c)]
  have hY : 4*y≤q^2 := by dsimp [q,y]; nlinarith only [sq_nonneg (b-d)]
  have hk := box_polynomial_nonneg p q x y hp hq hx hy hX hY
  have hHpos : 0<H := by dsimp [H]; positivity
  have hnum : 81*E*(p*q) ≤ (p+q)*(4*(p+q)*H) := by
    dsimp [E,H]
    nlinarith only [hk]
  have hratio : 81*E/(4*(p+q)*H) ≤ (p+q)/(p*q) :=
    (div_le_div_iff₀ (by positivity) (mul_pos hp hq)).2 hnum
  have hleft : 1/(c+a)+1/(b+d) = (p+q)/(p*q) := by
    dsimp [p,q]
    field_simp [ne_of_gt (add_pos hc ha),ne_of_gt (add_pos ha hc),ne_of_gt (add_pos hb hd)]
    <;> ring
  have hE : (a+b)*(b+c)*(c+d)*(d+a)=E := by dsimp [E,p,q,x,y]; ring
  have hH : (a+c+d)*(d+a+b)*(a+b+c)*(b+c+d)=H := by dsimp [H,p,q,x,y]; ring
  have hS : a+b+c+d=p+q := by dsimp [p,q]; ring
  have hden : (a+b+c+d)*(a+c+d)*(d+a+b)*(a+b+c)*(b+c+d)=(p+q)*H := by
    rw [← hS,← hH]
    ring
  have hN : (81/4:ℝ)*(a+b)*(b+c)*(c+d)*(d+a)=(81*E)/4 := by rw [← hE]; ring
  have hright : (81/4:ℝ)*(a+b)*(b+c)*(c+d)*(d+a)/
      ((a+b+c+d)*(a+c+d)*(d+a+b)*(a+b+c)*(b+c+d)) = 81*E/(4*(p+q)*H) := by
    rw [hN,hden,div_div]
    congr 1
    ring
  rw [hleft,hright]
  exact hratio

#print axioms solution
