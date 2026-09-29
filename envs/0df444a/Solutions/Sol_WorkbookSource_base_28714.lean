-- Prove2me | solution 1 for WorkbookSource.base_28714
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:04:47.61745+00:00
-- url     : https://prove2.me/submissions/2fab41ad-d997-4ec6-a0b9-2c6b2cb6ac2e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
private lemma cubic_pair_bound (p q : ℝ) (hp : 0<p) (hq : 0<q) :
    p*q*(p^2+q^2)^2 ≤ (p^3+q^3)^2 := by
  have he : (p^3+q^3)^2-p*q*(p^2+q^2)^2 =
      (p-q)^2*(p^4+p^3*q+p^2*q^2+p*q^3+q^4) := by ring
  have hn : 0 ≤ (p-q)^2*(p^4+p^3*q+p^2*q^2+p*q^3+q^4) := by positivity
  linarith only [he,hn]
private lemma product_bound (p q s t : ℝ) (hp : 0<p) (hq : 0<q) (hs : 0<s) (ht : 0<t)
    (hS : 4*p ≤ s^2) (hT : 4*q ≤ t^2) :
    4*p*q*(p^2+q^2) ≤ s*t*(p^3+q^3) := by
  have h0 := mul_le_mul hS hT (show 0≤4*q by positivity) (sq_nonneg s)
  have hST : 16*p*q ≤ s^2*t^2 := by nlinarith only [h0]
  have h1 := cubic_pair_bound p q hp hq
  have hm := mul_le_mul hST h1 (show 0≤p*q*(p^2+q^2)^2 by positivity)
    (show 0≤s^2*t^2 by positivity)
  have hsq : (4*p*q*(p^2+q^2))^2 ≤ (s*t*(p^3+q^3))^2 := by nlinarith only [hm]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^4 * c^2 + b^4 * d^2) / (c * d) + (b^4 * d^2 + c^4 * a^2) / (d * a) + (c^4 * a^2 + d^4 * b^2) / (a * b) + (d^4 * b^2 + a^4 * c^2) / (b * c) ≥ 4 * (a^2 * c^2 + b^2 * d^2)   := by
  let p := a*c
  let q := b*d
  let s := a+c
  let t := b+d
  have hp : 0<p := by dsimp [p]; positivity
  have hq : 0<q := by dsimp [q]; positivity
  have hs : 0<s := by dsimp [s]; positivity
  have ht : 0<t := by dsimp [t]; positivity
  have hS : 4*p ≤ s^2 := by dsimp [p,s]; nlinarith only [sq_nonneg (a-c)]
  have hT : 4*q ≤ t^2 := by dsimp [q,t]; nlinarith only [sq_nonneg (b-d)]
  have hbase := product_bound p q s t hp hq hs ht hS hT
  have hrest : 0 ≤ s*t*(p^2*(a-c)^2+q^2*(b-d)^2) := by positivity
  have hrat : (a^4*c^2+b^4*d^2)/(c*d)+(b^4*d^2+c^4*a^2)/(d*a)
      +(c^4*a^2+d^4*b^2)/(a*b)+(d^4*b^2+a^4*c^2)/(b*c)
      = s*t*(p^2*((a-c)^2+p)+q^2*((b-d)^2+q))/(p*q) := by
    dsimp [p,q,s,t]
    field_simp [ne_of_gt ha,ne_of_gt hb,ne_of_gt hc,ne_of_gt hd]
    <;> ring
  have hright : 4*(a^2*c^2+b^2*d^2)=4*(p^2+q^2) := by dsimp [p,q]; ring
  rw [hrat,hright]
  apply (le_div_iff₀ (mul_pos hp hq)).2
  nlinarith only [hbase,hrest]

#print axioms solution
