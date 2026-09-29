-- Prove2me | solution 1 for WorkbookSource.base_17392
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:49:46.92836+00:00
-- url     : https://prove2.me/submissions/bde0fddd-cebd-4ba8-9e9f-1f920b6d709f

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

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 + b^2 + c^2) / (a * b + b * c + c * d) + (b^2 + c^2 + d^2) / (b * c + c * d + d * a) + (a^2 + c^2 + d^2) / (a * b + a * d + c * d) + (a^2 + b^2 + d^2) / (a * b + a * d + b * c) ≥ 4  := by
  have hp1 : 0 < a*b+b*c+c*d := by positivity
  have hp2 : 0 < b*c+c*d+d*a := by positivity
  have hp3 : 0 < a*b+a*d+c*d := by positivity
  have hp4 : 0 < a*b+a*d+b*c := by positivity
  have hsq (p q r : ℝ) : (p+q+r)^2 ≤ 3*(p^2+q^2+r^2) := by
    nlinarith only [sq_nonneg (p-q),sq_nonneg (q-r),sq_nonneg (r-p)]
  have hdiv (p q r u : ℝ) (hu : 0 < u) :
      (p+q+r)^2/u ≤ 3*((p^2+q^2+r^2)/u) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hsq p q r) (le_of_lt hu)
  have h1 := hdiv a b c (a*b+b*c+c*d) hp1
  have h2 := hdiv b c d (b*c+c*d+d*a) hp2
  have h3 := hdiv a c d (a*b+a*d+c*d) hp3
  have h4 := hdiv a b d (a*b+a*d+b*c) hp4
  have ht := titu_four (a+b+c) (b+c+d) (a+c+d) (a+b+d)
    (a*b+b*c+c*d) (b*c+c*d+d*a) (a*b+a*d+c*d) (a*b+a*d+b*c) hp1 hp2 hp3 hp4
  have hl : 12 ≤ ((a+b+c)+(b+c+d)+(a+c+d)+(a+b+d))^2 /
      ((a*b+b*c+c*d)+(b*c+c*d+d*a)+(a*b+a*d+c*d)+(a*b+a*d+b*c)) := by
    apply (le_div_iff₀ (show 0 < (a*b+b*c+c*d)+(b*c+c*d+d*a)+(a*b+a*d+c*d)+(a*b+a*d+b*c) by positivity)).2
    nlinarith only [sq_nonneg (a+c-b-d)]
  linarith only [h1,h2,h3,h4,ht,hl]

#print axioms solution
