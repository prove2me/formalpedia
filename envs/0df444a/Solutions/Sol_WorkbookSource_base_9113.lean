-- Prove2me | solution 1 for WorkbookSource.base_9113
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:22:15.060096+00:00
-- url     : https://prove2.me/submissions/399a5b13-4319-436b-8632-b9a3d505c36b

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

private lemma titu_four (p q r s u v w x : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hx : 0 < x) :
    (p+q+r+s)^2/(u+v+w+x) ≤ p^2/u + q^2/v + r^2/w + s^2/x := by
  have h1 := titu_two p q u v hu hv
  have h2 := titu_two r s w x hw hx
  have h3 := titu_two (p+q) (r+s) (u+v) (w+x) (add_pos hu hv) (add_pos hw hx)
  have he : (p+q)+(r+s) = p+q+r+s := by ring
  have hd : (u+v)+(w+x) = u+v+w+x := by ring
  rw [he, hd] at h3
  linarith

private lemma cubic_young (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    3*u*v^2 ≤ u^3 + 2*v^3 := by
  have h := mul_nonneg (sq_nonneg (u-v)) (show 0 ≤ u+2*v by positivity)
  nlinarith only [h]

private lemma quartic_young (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v) :
    4*u^3 ≤ 3*(u^4/v)+v^3 := by
  have hp : 0 ≤ (u-v)^2*(3*u^2+2*u*v+v^2) := by positivity
  have he : (u-v)^2*(3*u^2+2*u*v+v^2) = 3*u^4-4*u^3*v+v^4 := by ring
  rw [he] at hp
  have hq : (u^4/v)*v = u^4 := div_mul_cancel₀ _ (ne_of_gt hv)
  have h := (le_div_iff₀ hv).2 (show (4*u^3-v^3)*v ≤ 3*u^4 by nlinarith only [hp])
  rw [mul_div_assoc] at h
  linarith

private lemma reciprocal_pair (u v : ℝ) (hu : 0<u) (hv : 0<v) (h : u*v=1) : 2≤u+v := by
  have hs : (2:ℝ)^2≤(u+v)^2 := by nlinarith only [h,sq_nonneg (u-v)]
  exact (sq_le_sq₀ (by norm_num) (le_of_lt (add_pos hu hv))).mp hs
private lemma four_ratio_bound (p q r s : ℝ) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (h : p*q*r*s=1) : p^2+q^2+r^2+s^2+12≤(p+q+r+s)^2 := by
  have h1 := reciprocal_pair (p*q) (r*s) (mul_pos hp hq) (mul_pos hr hs) (by nlinarith only [h])
  have h2 := reciprocal_pair (p*r) (q*s) (mul_pos hp hr) (mul_pos hq hs) (by nlinarith only [h])
  have h3 := reciprocal_pair (p*s) (q*r) (mul_pos hp hs) (mul_pos hq hr) (by nlinarith only [h])
  nlinarith only [h1,h2,h3]
private lemma normalize_fraction (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    a/(a+3*b^2) = (a/b)^2/((a/b)^2+3*a) := by
  apply (div_eq_div_iff (ne_of_gt (show 0<a+3*b^2 by positivity))
    (ne_of_gt (show 0<(a/b)^2+3*a by positivity))).2
  field_simp [ne_of_gt hb]
  <;> ring

theorem solution (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (habc : a + b + c + d = 4) : a / (a + 3 * b ^ 2) + b / (b + 3 * c ^ 2) + c / (c + 3 * d ^ 2) + d / (d + 3 * a ^ 2) ≥ 1   := by
  let p := a/b
  let q := b/c
  let r := c/d
  let s := d/a
  have hp : 0<p := by dsimp [p]; positivity
  have hq : 0<q := by dsimp [q]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hs : 0<s := by dsimp [s]; positivity
  have hprod : p*q*r*s=1 := by
    dsimp [p,q,r,s]
    field_simp [ne_of_gt ha,ne_of_gt hb,ne_of_gt hc,ne_of_gt hd]
    <;> ring
  have hbound := four_ratio_bound p q r s hp hq hr hs hprod
  have hd1 : 0<p^2+3*a := by positivity
  have hd2 : 0<q^2+3*b := by positivity
  have hd3 : 0<r^2+3*c := by positivity
  have hd4 : 0<s^2+3*d := by positivity
  have ht := titu_four p q r s (p^2+3*a) (q^2+3*b) (r^2+3*c) (s^2+3*d) hd1 hd2 hd3 hd4
  have hl : 1≤(p+q+r+s)^2/((p^2+3*a)+(q^2+3*b)+(r^2+3*c)+(s^2+3*d)) := by
    apply (le_div_iff₀ (show 0<(p^2+3*a)+(q^2+3*b)+(r^2+3*c)+(s^2+3*d) by positivity)).2
    nlinarith only [hbound,habc]
  have h1 : a/(a+3*b^2)=p^2/(p^2+3*a) := normalize_fraction a b ha hb
  have h2 : b/(b+3*c^2)=q^2/(q^2+3*b) := normalize_fraction b c hb hc
  have h3 : c/(c+3*d^2)=r^2/(r^2+3*c) := normalize_fraction c d hc hd
  have h4 : d/(d+3*a^2)=s^2/(s^2+3*d) := normalize_fraction d a hd ha
  rw [h1,h2,h3,h4]
  exact hl.trans ht

#print axioms solution
