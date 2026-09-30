-- Prove2me | solution 1 for TranscendenceTheory.bounded_rational_congruence_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T22:49:23.41288+00:00
-- url     : https://prove2.me/submissions/4a556aca-597f-4b01-b9ed-df882c841e83

import Mathlib.Algebra.Polynomial.Div

open Polynomial

private lemma polynomial_congruence_zero {R : Type*} [CommRing R]
    (B : Polynomial R) (s : ℕ) (hdeg : B.natDegree ≤ s) :
    X ^ (s + 1) ∣ B ↔ B = 0 := by
  constructor
  · intro h
    apply Polynomial.ext
    intro i
    rw [coeff_zero]
    by_cases hi : i < s + 1
    · exact (Polynomial.X_pow_dvd_iff.mp h) i hi
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · rintro rfl
    exact dvd_zero _

theorem solution
    (R : Type*) [CommRing R] (Q A : Polynomial R) (α z : R) (d s : ℕ)
    (hQ : Q.natDegree ≤ d) (hA : A.degree < (d : WithBot ℕ)) (hds : d ≤ s) :
    X ^ (s + 1) ∣ (1 - C z * X) * A - C α * Q ↔
      (1 - C z * X) * A = C α * Q := by
  have hprod : ((1 - C z * X) * A).natDegree ≤ d := by
    by_cases ha : A = 0
    · simp [ha]
    · have hn : A.natDegree < d := (natDegree_lt_iff_degree_lt ha).mpr hA
      have hf : (1 - C z * X : Polynomial R).natDegree ≤ 1 := by
        apply (natDegree_sub_le _ _).trans
        exact max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      exact natDegree_mul_le.trans (by omega)
  have hdeg : ((1 - C z * X) * A - C α * Q).natDegree ≤ s :=
    (natDegree_sub_le _ _).trans
      ((max_le hprod ((natDegree_C_mul_le _ _).trans hQ)).trans hds)
  rw [polynomial_congruence_zero _ s hdeg, sub_eq_zero]
