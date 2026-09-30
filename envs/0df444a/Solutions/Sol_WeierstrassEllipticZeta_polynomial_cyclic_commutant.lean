-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_cyclic_commutant
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T20:45:41.513099+00:00
-- url     : https://prove2.me/submissions/59934c2a-4477-44d7-97f7-4221935473dd

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Bilinear



theorem solution
    (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
    (x : A)
    (hx : Function.Surjective (fun q : Polynomial R => q.eval₂ (algebraMap R A) x))
    (T : A →ₗ[R] A) :
    (∀ a : A, T (x * a) = x * T a) ↔
      ∃! b : A, T = Algebra.lmul R A b := by
  constructor
  · intro hT
    have hpow (n : ℕ) : T (x ^ n) = x ^ n * T 1 := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', hT, ih, mul_assoc]
    have hpoly (q : Polynomial R) :
        T (q.eval₂ (algebraMap R A) x) = q.eval₂ (algebraMap R A) x * T 1 := by
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq, add_mul]
      | monomial n r =>
        rw [Polynomial.eval₂_monomial, ← Algebra.smul_def, T.map_smul, hpow]
        simp only [Algebra.smul_def, mul_assoc]
    have hform : T = Algebra.lmul R A (T 1) := by
      ext a
      obtain ⟨q, rfl⟩ := hx a
      exact (hpoly q).trans (mul_comm _ _)
    refine ⟨T 1, hform, ?_⟩
    intro b hb
    have h := LinearMap.congr_fun hb 1
    simpa using h.symm
  · rintro ⟨b, rfl, _⟩ a
    change b * (x * a) = x * (b * a)
    exact mul_left_comm b x a

