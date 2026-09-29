-- Prove2me | solution 1 for WorkbookSource.base_31243
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:49:46.046366+00:00
-- url     : https://prove2.me/submissions/6bf8101a-02d8-4d46-afeb-afd165417f01

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open Real Nat

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

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (b * (-d + 2 * b - c) / (b + c + d) + c * (-d + 2 * c - a) / (c + d + a) + d * (2 * d - b - a) / (d + a + b) + a * (2 * a - b - c) / (a + b + c)) ≥ 0  := by
  have hp1 : 0 < b+c+d := by positivity
  have hp2 : 0 < c+d+a := by positivity
  have hp3 : 0 < d+a+b := by positivity
  have hp4 : 0 < a+b+c := by positivity
  have hs : 0 < a+b+c+d := by positivity
  have ht := titu_four b c d a (b+c+d) (c+d+a) (d+a+b) (a+b+c) hp1 hp2 hp3 hp4
  have he : (b+c+d+a)^2/((b+c+d)+(c+d+a)+(d+a+b)+(a+b+c)) = (a+b+c+d)/3 := by
    have hden : (b+c+d)+(c+d+a)+(d+a+b)+(a+b+c) = 3*(a+b+c+d) := by ring
    rw [hden]
    field_simp [ne_of_gt hs]
    <;> ring
  rw [he] at ht
  have h1 : b*(-d+2*b-c)/(b+c+d) = 3*(b^2/(b+c+d))-b := by
    field_simp [ne_of_gt hp1]
    <;> ring
  have h2 : c*(-d+2*c-a)/(c+d+a) = 3*(c^2/(c+d+a))-c := by
    field_simp [ne_of_gt hp2]
    <;> ring
  have h3 : d*(2*d-b-a)/(d+a+b) = 3*(d^2/(d+a+b))-d := by
    field_simp [ne_of_gt hp3]
    <;> ring
  have h4 : a*(2*a-b-c)/(a+b+c) = 3*(a^2/(a+b+c))-a := by
    field_simp [ne_of_gt hp4]
    <;> ring
  rw [h1,h2,h3,h4]
  linarith only [ht]

#print axioms solution
