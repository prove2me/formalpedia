-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_nilpotent_fiber_calculus
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T23:44:13.931542+00:00
-- url     : https://prove2.me/submissions/3864a490-101d-4bad-9bef-e66e2de21083

import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Nilpotent.Basic



theorem solution
    (K A : Type*) [Field K] [CommRing A] [Nontrivial A]
    (φ : K →+* A) (x : A) (z : K) (d : ℕ) (hx : (x - φ z) ^ d = 0)
    (q : Polynomial K) :
    (q.eval₂ φ x - φ (q.eval z)) ^ d = 0 ∧
      (IsUnit (q.eval₂ φ x) ↔ q.eval z ≠ 0) ∧
      (IsNilpotent (q.eval₂ φ x) ↔ q.eval z = 0) := by
  obtain ⟨r, hr⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := q) (a := z)
  have heval : q.eval₂ φ x - φ (q.eval z) = (x - φ z) * r.eval₂ φ x := by
    have h := congrArg (Polynomial.eval₂ φ x) hr
    simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_C,
      Polynomial.eval₂_mul, Polynomial.eval₂_X] using h
  have hpow : (q.eval₂ φ x - φ (q.eval z)) ^ d = 0 := by
    rw [heval, mul_pow, hx, zero_mul]
  have hnil : IsNilpotent (q.eval₂ φ x - φ (q.eval z)) := ⟨d, hpow⟩
  have hunit : IsUnit (q.eval₂ φ x) ↔ q.eval z ≠ 0 := by
    constructor
    · intro hu hq
      have hn : IsNilpotent (q.eval₂ φ x) := by simpa [hq] using hnil
      exact hn.not_isUnit hu
    · intro hq
      have hu : IsUnit (φ (q.eval z)) := (isUnit_iff_ne_zero.mpr hq).map φ
      have h := hnil.isUnit_add_right_of_commute hu (Commute.all _ _)
      simpa only [sub_add_cancel] using h
  refine ⟨hpow, hunit, ?_⟩
  constructor
  · intro hn
    by_contra hq
    exact hn.not_isUnit (hunit.mpr hq)
  · intro hq
    simpa [hq] using hnil

