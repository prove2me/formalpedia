-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_monic_evaluation_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T02:23:24.438753+00:00
-- url     : https://prove2.me/submissions/e8a32ce2-de1b-4bc7-bae6-8a8ddea5416e

import Mathlib.Algebra.Polynomial.Div



theorem solution
    (K A : Type*) [Field K] [CommRing A]
    (φ : K →+* A) (x : A) (m : Polynomial K) (hm : m.Monic)
    (hker : ∀ q : Polynomial K, q.eval₂ φ x = 0 ↔ m ∣ q) :
    (∀ q : Polynomial K,
      (q %ₘ m).degree < m.degree ∧ (q %ₘ m).eval₂ φ x = q.eval₂ φ x ∧
        ∀ r : Polynomial K, r.degree < m.degree → r.eval₂ φ x = q.eval₂ φ x →
          r = q %ₘ m) ∧
      ∀ q r : Polynomial K, q.eval₂ φ x = r.eval₂ φ x ↔ q %ₘ m = r %ₘ m := by
  have hmroot : m.eval₂ φ x = 0 := (hker m).mpr dvd_rfl
  have hmod : ∀ q : Polynomial K, (q %ₘ m).eval₂ φ x = q.eval₂ φ x :=
    fun _ => Polynomial.eval₂_modByMonic_eq_self_of_root hmroot
  have hcongr : ∀ q r : Polynomial K,
      q.eval₂ φ x = r.eval₂ φ x ↔ q %ₘ m = r %ₘ m := by
    intro q r
    constructor
    · intro h
      have hz : (q - r).eval₂ φ x = 0 := by
        rw [Polynomial.eval₂_sub, h, sub_self]
      exact Polynomial.modByMonic_eq_of_dvd_sub hm ((hker _).mp hz)
    · intro h
      exact (hmod q).symm.trans ((congrArg (Polynomial.eval₂ φ x) h).trans (hmod r))
  refine ⟨?_, hcongr⟩
  intro q
  refine ⟨Polynomial.degree_modByMonic_lt q hm, hmod q, ?_⟩
  intro r hr heq
  have h := (hcongr r q).mp heq
  rwa [(Polynomial.modByMonic_eq_self_iff hm).mpr hr] at h

