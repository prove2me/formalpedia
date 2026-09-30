-- Prove2me | solution 1 for TranscendenceTheory.affine_coordinate_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T20:28:25.0855+00:00
-- url     : https://prove2.me/submissions/0bc142c8-94a6-456c-b088-4f0ec6935965

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv

open MvPolynomial

private lemma monomial_aeval_update
    {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [DecidableEq σ] (v : σ → S) (i : σ) (t : S) (d : σ →₀ ℕ) (c : R)
    (hd : d i = 0) :
    aeval (Function.update v i t) (monomial d c) = aeval v (monomial d c) := by
  simp only [aeval_monomial]
  congr 1
  apply Finsupp.prod_congr
  intro j hj
  have hji : j ≠ i := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hj) hd
  rw [Function.update_of_ne hji]

private lemma monomial_affine_evaluation
    {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [DecidableEq σ] (v : σ → S) (i : σ) (d : σ →₀ ℕ) (c : R)
    (hd : d i ≤ 1) :
    aeval v (monomial d c) =
      aeval (Function.update v i 0) (monomial d c) +
        v i * aeval (Function.update v i 0) (pderiv i (monomial d c)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hd | hd
  · simp [pderiv_monomial, hd, monomial_aeval_update v i 0 d c hd]
  · have hfactor : X i * pderiv i (monomial d c) = monomial d c := by
      simpa [hd] using (X_mul_pderiv_monomial (i := i) (m := d) (r := c))
    have hderiv : aeval (Function.update v i 0) (pderiv i (monomial d c)) =
        aeval v (pderiv i (monomial d c)) := by
      simp only [pderiv_monomial]
      apply monomial_aeval_update
      simp [hd]
    have hzero : aeval (Function.update v i 0) (monomial d c) = 0 := by
      conv_lhs => rw [← hfactor]
      simp
    rw [hzero, zero_add, hderiv]
    simpa using (congrArg (aeval v) hfactor).symm

theorem solution
    (R S σ : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
    [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) (v : σ → S)
    (hp : p.degreeOf i ≤ 1) :
    MvPolynomial.aeval v p =
      MvPolynomial.aeval (Function.update v i 0) p +
        v i * MvPolynomial.aeval (Function.update v i 0) (MvPolynomial.pderiv i p) := by
  have hm := degreeOf_le_iff.mp hp
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  exact monomial_affine_evaluation v i d (coeff d p) (hm d hd)
