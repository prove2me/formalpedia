-- Prove2me | solution 1 for WorkbookSource.plus_10465
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:22:15.817586+00:00
-- url     : https://prove2.me/submissions/43eb53dc-c6ca-4bfa-afb4-dcdcbe63614c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
private lemma titu_two (p q u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (p + q)^2 / (u + v) ≤ p^2/u + q^2/v := by
  have hi : p^2/u + q^2/v - (p+q)^2/(u+v) =
      (p*v-q*u)^2/(u*v*(u+v)) := by
    field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt (add_pos hu hv)]
    <;> ring
  have hn : 0 ≤ (p*v-q*u)^2/(u*v*(u+v)) :=
    div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (mul_pos hu hv) (add_pos hu hv)))
  linarith


private lemma titu_three (p q r u v w : ℝ) (hu : 0<u) (hv : 0<v) (hw : 0<w) :
    (p+q+r)^2/(u+v+w) ≤ p^2/u+q^2/v+r^2/w := by
  have h1 := titu_two p q u v hu hv
  have h2 := titu_two (p+q) r (u+v) w (add_pos hu hv) hw
  linarith only [h1,h2]
private lemma cancel_square (p q : ℝ) (hp : 0<p) (hq : 0<q) : p^2/(p*q)=p/q := by
  field_simp [ne_of_gt hp,ne_of_gt hq]
  <;> ring
private lemma scalar_bound (q : ℝ) (hq : 0<q) (h3 : q≤3) : 5≤9/q+6/(6-q) := by
  have hr : 0<6-q := by linarith
  have he : 9/q+6/(6-q)-5 = (3-q)*(18-5*q)/(q*(6-q)) := by
    field_simp [ne_of_gt hq,ne_of_gt hr]
    <;> ring
  have hn : 0≤(3-q)*(18-5*q)/(q*(6-q)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith only [he,hn]

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 9 / (a * b + b * c + c * a) + (a + b) / (a ^ 2 + a * b + c) + (b + c) / (b ^ 2 + b * c + a) + (c + a) / (c ^ 2 + c * a + b) ≥ 5    := by
  let q := a*b+b*c+c*a
  let C := a^2*b+b^2*c+c^2*a
  let D := (a+b)*(a^2+a*b+c)+(b+c)*(b^2+b*c+a)+(c+a)*(c^2+c*a+b)
  have hq : 0<q := by dsimp [q]; positivity
  have hS2 : (a+b+c)^2=9 := by rw [hab]; norm_num
  have hq3 : q≤3 := by
    dsimp [q]
    nlinarith only [hS2,sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have hC : C≤a^2+b^2+c^2 := by
    have he : (a+b+c)*(a^2+b^2+c^2)-3*C = a*(a-b)^2+b*(b-c)^2+c*(c-a)^2 := by dsimp [C]; ring
    have hn : 0≤a*(a-b)^2+b*(b-c)^2+c*(c-a)^2 := by positivity
    rw [hab] at he
    linarith only [he,hn]
  have hsum : a^2+b^2+c^2=9-2*q := by dsimp [q]; nlinarith only [hS2]
  have hD : D=(a+b+c)^3-2*(a+b+c)*q+C+2*q := by dsimp [D,q,C]; ring
  rw [hab] at hD
  have hDup : D≤6*(6-q) := by norm_num at hD; linarith only [hD,hC,hsum]
  have hDpos : 0<D := by dsimp [D]; positivity
  have hr : 0<6-q := by linarith
  have ht := titu_three (a+b) (b+c) (c+a)
    ((a+b)*(a^2+a*b+c)) ((b+c)*(b^2+b*c+a)) ((c+a)*(c^2+c*a+b))
    (by positivity) (by positivity) (by positivity)
  have hn : ((a+b)+(b+c)+(c+a))^2=36 := by
    have he : (a+b)+(b+c)+(c+a)=6 := by linarith only [hab]
    rw [he]
    norm_num
  rw [hn,cancel_square (a+b) (a^2+a*b+c) (by positivity) (by positivity),
    cancel_square (b+c) (b^2+b*c+a) (by positivity) (by positivity),
    cancel_square (c+a) (c^2+c*a+b) (by positivity) (by positivity)] at ht
  change 36/D ≤ (a+b)/(a^2+a*b+c)+(b+c)/(b^2+b*c+a)+(c+a)/(c^2+c*a+b) at ht
  have hlo : 6/(6-q)≤36/D := by
    apply (div_le_div_iff₀ hr hDpos).2
    linarith only [hDup]
  have hs := scalar_bound q hq hq3
  change 9/q+(a+b)/(a^2+a*b+c)+(b+c)/(b^2+b*c+a)+(c+a)/(c^2+c*a+b)≥5
  linarith only [hs,hlo,ht]

#print axioms solution
