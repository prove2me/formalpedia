-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_nilpotent_derivative_calculus
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T03:53:02.541508+00:00
-- url     : https://prove2.me/submissions/a8f0440c-465d-4580-bc88-2b755a4dd78e

import Theorems.Thm_WeierstrassEllipticZeta_polynomial_nilpotent_taylor_calculus
import Mathlib.Algebra.Polynomial.HasseDeriv



theorem solution
    (K A : Type*) [Field K] [CharZero K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (n : ℕ)
    (hker : ∀ q : Polynomial K,
      q.eval₂ φ x = 0 ↔ (Polynomial.X - Polynomial.C z) ^ n ∣ q) :
    (∀ q : Polynomial K, q.eval₂ φ x =
      ∑ i ∈ Finset.range n,
        φ (((Polynomial.derivative^[i]) q).eval z / (i.factorial : K)) * (x - φ z) ^ i) ∧
    (∀ q : Polynomial K,
      q.eval₂ φ x = 0 ↔ ∀ i < n, ((Polynomial.derivative^[i]) q).eval z = 0) ∧
    ∀ q r : Polynomial K, q.eval₂ φ x = r.eval₂ φ x ↔
      ∀ i < n, ((Polynomial.derivative^[i]) q).eval z =
        ((Polynomial.derivative^[i]) r).eval z := by
  have hfac (i : ℕ) : (i.factorial : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hderiv (q : Polynomial K) (i : ℕ) :
      ((Polynomial.derivative^[i]) q).eval z =
        (i.factorial : K) * (Polynomial.hasseDeriv i q).eval z := by
    have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := i)) q
    change i.factorial • (Polynomial.hasseDeriv i q) = (Polynomial.derivative^[i]) q at h
    simpa only [nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast] using
      (congrArg (Polynomial.eval z) h).symm
  have hnorm (q : Polynomial K) (i : ℕ) :
      (Polynomial.hasseDeriv i q).eval z =
        ((Polynomial.derivative^[i]) q).eval z / (i.factorial : K) := by
    apply (eq_div_iff (hfac i)).mpr
    rw [hderiv, mul_comm]
  have hzero (q : Polynomial K) (i : ℕ) :
      (Polynomial.hasseDeriv i q).eval z = 0 ↔
        ((Polynomial.derivative^[i]) q).eval z = 0 := by
    simp only [hderiv, mul_eq_zero, hfac, false_or]
  have heq (q r : Polynomial K) (i : ℕ) :
      (Polynomial.hasseDeriv i q).eval z = (Polynomial.hasseDeriv i r).eval z ↔
        ((Polynomial.derivative^[i]) q).eval z = ((Polynomial.derivative^[i]) r).eval z := by
    simp only [hderiv, mul_right_inj' (hfac i)]
  obtain ⟨hTaylor, hjet, hjet_eq⟩ :=
    WeierstrassEllipticZeta.polynomial_nilpotent_taylor_calculus K A φ x z n hker
  exact ⟨by simpa only [hnorm] using hTaylor,
    by simpa only [hzero] using hjet,
    by simpa only [heq] using hjet_eq⟩

