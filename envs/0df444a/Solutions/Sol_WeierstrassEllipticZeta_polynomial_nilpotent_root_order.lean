-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_nilpotent_root_order
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T00:31:39.929419+00:00
-- url     : https://prove2.me/submissions/6e1691f0-59e6-426f-ac0d-97189dcc84ee

import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Nilpotent.Basic



theorem solution
    (K A : Type*) [Field K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (d : ℕ) (hx : (x - φ z) ^ d = 0)
    (q : Polynomial K) (hq : q ≠ 0) :
    ∃ u : Aˣ,
      q.eval₂ φ x = (x - φ z) ^ q.rootMultiplicity z * (u : A) ∧
      (∀ k : ℕ, (q.eval₂ φ x) ^ k = 0 ↔
        (x - φ z) ^ (q.rootMultiplicity z * k) = 0) ∧
      ∀ k : ℕ, d ≤ q.rootMultiplicity z * k → (q.eval₂ φ x) ^ k = 0 := by
  let r := q /ₘ (Polynomial.X - Polynomial.C z) ^ q.rootMultiplicity z
  have hr : r.eval z ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hq
  have hfactor : q.eval₂ φ x = (x - φ z) ^ q.rootMultiplicity z * r.eval₂ φ x := by
    have h := congrArg (Polynomial.eval₂ φ x) (q.pow_mul_divByMonic_rootMultiplicity_eq z)
    simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C] using h.symm
  obtain ⟨s, hs⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := r) (a := z)
  have hdiff : r.eval₂ φ x - φ (r.eval z) = (x - φ z) * s.eval₂ φ x := by
    have h := congrArg (Polynomial.eval₂ φ x) hs
    simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_X] using h
  have hn : IsNilpotent (r.eval₂ φ x - φ (r.eval z)) := by
    refine ⟨d, ?_⟩
    rw [hdiff, mul_pow, hx, zero_mul]
  have hu : IsUnit (r.eval₂ φ x) := by
    have hc : IsUnit (φ (r.eval z)) := (isUnit_iff_ne_zero.mpr hr).map φ
    simpa only [sub_add_cancel] using
      hn.isUnit_add_right_of_commute hc (Commute.all _ _)
  obtain ⟨u, hu⟩ := hu
  have heq : q.eval₂ φ x = (x - φ z) ^ q.rootMultiplicity z * (u : A) := by
    rw [hu]
    exact hfactor
  have hiff : ∀ k : ℕ, (q.eval₂ φ x) ^ k = 0 ↔
      (x - φ z) ^ (q.rootMultiplicity z * k) = 0 := by
    intro k
    rw [heq, mul_pow, ← pow_mul]
    exact (u.isUnit.pow k).mul_left_eq_zero
  exact ⟨u, heq, hiff, fun k hk => (hiff k).mpr (pow_eq_zero_of_le hk hx)⟩

