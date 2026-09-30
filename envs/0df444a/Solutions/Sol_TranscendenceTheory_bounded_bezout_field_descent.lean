-- Prove2me | solution 1 for TranscendenceTheory.bounded_bezout_field_descent
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T22:53:39.765981+00:00
-- url     : https://prove2.me/submissions/13a75349-74d8-427b-8787-7a0345824e54

import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

theorem solution
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (f g h : Polynomial K) (a b c : ℕ) :
    (∃ u v w : Polynomial L,
      u * f.map (algebraMap K L) + v * g.map (algebraMap K L) +
          w * h.map (algebraMap K L) = 1 ∧
      v.natDegree < b ∧ w.natDegree < c ∧ u.natDegree ≤ a) ↔
    (∃ u v w : Polynomial K,
      u * f + v * g + w * h = 1 ∧
      v.natDegree < b ∧ w.natDegree < c ∧ u.natDegree ≤ a) := by
  classical
  obtain ⟨r, hr⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  let π : Polynomial L →ₗ[K] Polynomial K :=
    (PolynomialModule.equivPolynomial (R := K) (S := K)).toLinearMap.comp
      ((PolynomialModule.map K r).comp
        (PolynomialModule.equivPolynomial (R := K) (S := L)).symm.toLinearMap)
  have hcoeff (p : Polynomial L) (n : ℕ) : (π p).coeff n = r (p.coeff n) := rfl
  have hr_base (x : K) : r (algebraMap K L x) = x := by
    rw [show algebraMap K L x = x • (1 : L) by simp [Algebra.smul_def],
      map_smul, hr, smul_eq_mul, mul_one]
  have hbase (p : Polynomial K) : π (p.map (algebraMap K L)) = p := by
    ext n
    rw [hcoeff, Polynomial.coeff_map, hr_base]
  have hone : π 1 = 1 := by simpa only [Polynomial.map_one] using hbase 1
  have hmul (u : Polynomial L) (p : Polynomial K) :
      π (u * p.map (algebraMap K L)) = π u * p := by
    ext n
    simp only [hcoeff, Polynomial.coeff_mul, Polynomial.coeff_map, map_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [mul_comm (u.coeff ij.1), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hdegree (p : Polynomial L) : (π p).natDegree ≤ p.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt hn, map_zero]
  constructor
  · rintro ⟨u, v, w, hid, hv, hw, hu⟩
    refine ⟨π u, π v, π w, ?_, (hdegree v).trans_lt hv,
      (hdegree w).trans_lt hw, (hdegree u).trans hu⟩
    have heq := congrArg π hid
    simpa only [map_add, hmul, hone] using heq
  · rintro ⟨u, v, w, hid, hv, hw, hu⟩
    refine ⟨u.map (algebraMap K L), v.map (algebraMap K L), w.map (algebraMap K L),
      ?_, ?_, ?_, ?_⟩
    · simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] using
        congrArg (Polynomial.map (algebraMap K L)) hid
    · simpa only [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective] using hv
    · simpa only [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective] using hw
    · simpa only [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective] using hu
