-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_nilpotent_taylor_calculus
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T03:13:44.896097+00:00
-- url     : https://prove2.me/submissions/f9bd885f-6c60-4e26-813a-522db819e2f3

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div



theorem solution
    (K A : Type*) [CommRing K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (n : ℕ)
    (hker : ∀ q : Polynomial K,
      q.eval₂ φ x = 0 ↔ (Polynomial.X - Polynomial.C z) ^ n ∣ q) :
    (∀ q : Polynomial K, q.eval₂ φ x =
      ∑ i ∈ Finset.range n, φ ((Polynomial.hasseDeriv i q).eval z) * (x - φ z) ^ i) ∧
    (∀ q : Polynomial K,
      q.eval₂ φ x = 0 ↔ ∀ i < n, (Polynomial.hasseDeriv i q).eval z = 0) ∧
    ∀ q r : Polynomial K, q.eval₂ φ x = r.eval₂ φ x ↔
      ∀ i < n, (Polynomial.hasseDeriv i q).eval z = (Polynomial.hasseDeriv i r).eval z := by
  classical
  have hy : (x - φ z) ^ n = 0 := by
    have h := (hker ((Polynomial.X - Polynomial.C z) ^ n)).mpr dvd_rfl
    simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C] using h
  have hjet (q : Polynomial K) :
      q.eval₂ φ x = 0 ↔ ∀ i < n, (Polynomial.hasseDeriv i q).eval z = 0 := by
    rw [hker, ← map_dvd_iff (Polynomial.taylorEquiv z)]
    change Polynomial.taylor z ((Polynomial.X - Polynomial.C z) ^ n) ∣
      Polynomial.taylor z q ↔ _
    simp only [Polynomial.taylor_pow, map_sub,
      Polynomial.taylor_X, Polynomial.taylor_C, add_sub_cancel_right,
      Polynomial.X_pow_dvd_iff, Polynomial.taylor_coeff]
  refine ⟨?_, hjet, ?_⟩
  · intro q
    have ht : (Polynomial.taylor z q).eval₂ φ (x - φ z) = q.eval₂ φ x := by
      simp only [Polynomial.taylor_apply, Polynomial.eval₂_comp, Polynomial.eval₂_add,
        Polynomial.eval₂_X, Polynomial.eval₂_C, sub_add_cancel]
    rw [← ht, Polynomial.eval₂_eq_sum_range' φ
      (lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right n _))]
    rw [← Finset.sum_subset (Finset.range_mono (Nat.le_max_left n
      ((Polynomial.taylor z q).natDegree + 1))) ?_]
    · simp only [Polynomial.taylor_coeff]
    · intro i hi hin
      have hn : n ≤ i := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hin)
      rw [pow_eq_zero_of_le hn hy, mul_zero]
  · intro q r
    rw [← sub_eq_zero, ← Polynomial.eval₂_sub, hjet]
    simp only [map_sub, Polynomial.eval_sub, sub_eq_zero]

