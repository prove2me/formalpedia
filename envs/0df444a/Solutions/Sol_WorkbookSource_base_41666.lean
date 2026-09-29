-- Prove2me | solution 1 for WorkbookSource.base_41666
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:49:45.259009+00:00
-- url     : https://prove2.me/submissions/37075b11-877e-4208-b260-3e29c73d60b4

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

theorem solution (w x y z : ℝ) (hw : 0 < w) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (w^4 / z + x^4 / w + y^4 / x + z^4 / y) ≥ w * z^2 + x * w^2 + y * x^2 + z * y^2  := by
  have h1 := quartic_young w z (le_of_lt hw) hz
  have h2 := quartic_young x w (le_of_lt hx) hw
  have h3 := quartic_young y x (le_of_lt hy) hx
  have h4 := quartic_young z y (le_of_lt hz) hy
  have h5 := cubic_young w z (le_of_lt hw) (le_of_lt hz)
  have h6 := cubic_young x w (le_of_lt hx) (le_of_lt hw)
  have h7 := cubic_young y x (le_of_lt hy) (le_of_lt hx)
  have h8 := cubic_young z y (le_of_lt hz) (le_of_lt hy)
  linarith only [h1,h2,h3,h4,h5,h6,h7,h8]

#print axioms solution
