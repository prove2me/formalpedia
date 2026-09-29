-- Prove2me | solution 1 for WorkbookCorrected.plus_27694
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:03:44.897742+00:00
-- url     : https://prove2.me/submissions/04aa4122-d8fc-4a88-ba20-b3f2d0ccce8d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma tangent (a t : ℝ) (ha : 0<a) (ht : 0<t) : 3*t^2-2*t^3/a ≤ a^2 := by
  have hi : a*(a^2-(3*t^2-2*t^3/a))=(a-t)^2*(a+2*t) := by
    field_simp
    <;> ring
  have hp : 0 ≤ (a-t)^2*(a+2*t) := by positivity
  have hm : 0 ≤ a*(a^2-(3*t^2-2*t^3/a)) := by linarith only [hi,hp]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp hm)
private lemma bound (u v a b : ℝ) (hu : 0<u) (hv : 0<v) (ha : 0<a) (hb : 0<b)
    (h : u^3/a+v^3/b=1) : (u^2+v^2)^3 ≤ a^2+b^2 := by
  let s := u^2+v^2
  have hs : 0<s := by dsimp [s]; positivity
  have h1 := tangent a (u*s) ha (mul_pos hu hs)
  have h2 := tangent b (v*s) hb (mul_pos hv hs)
  have he : 2*(u*s)^3/a+2*(v*s)^3/b=2*s^3 := by
    calc
      _=2*s^3*(u^3/a+v^3/b) := by ring
      _=2*s^3 := by rw [h]; ring
  have hi : (u*s)^2+(v*s)^2=s^3 := by dsimp [s]; ring
  nlinarith only [h1,h2,he,hi]
theorem solution (u v : ℝ) (hu : 0<u) (hv : 0<v) (hu3 : u^3=2) (hv3 : v^3=3) :
    (∀ a b : ℝ, 0<a → 0<b → 2/a+3/b=1 → (u^2+v^2)^3 ≤ a^2+b^2) ∧
    (∃ a b : ℝ, 0<a ∧ 0<b ∧ 2/a+3/b=1 ∧ a^2+b^2=(u^2+v^2)^3) := by
  constructor
  · intro a b ha hb h
    apply bound u v a b hu hv ha hb
    simpa only [hu3,hv3] using h
  · let s := u^2+v^2
    have hs : 0<s := by dsimp [s]; positivity
    refine ⟨u*s,v*s,mul_pos hu hs,mul_pos hv hs,?_,?_⟩
    · rw [← hu3,← hv3]
      have he : u^3/(u*s)+v^3/(v*s)=(u^2+v^2)/s := by
        field_simp
        <;> ring
      rw [he]
      exact div_self (ne_of_gt hs)
    · dsimp [s]
      ring
example : (∀ (u v : ℝ) (hu : 0<u) (hv : 0<v) (hu3 : u^3=2) (hv3 : v^3=3),
    (∀ a b : ℝ, 0<a → 0<b → 2/a+3/b=1 → (u^2+v^2)^3 ≤ a^2+b^2) ∧
    (∃ a b : ℝ, 0<a ∧ 0<b ∧ 2/a+3/b=1 ∧ a^2+b^2=(u^2+v^2)^3)) := @solution
#print axioms solution
