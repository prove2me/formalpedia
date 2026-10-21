-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P03.multivar_as_univar
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:56:34.745563+00:00
-- url     : https://prove2.me/submissions/fee17a00-5099-4dc3-805a-c116038bb2d6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P03

open QAlgorithms.Papers.Independent.Next46.P03

theorem g62s_partA {R : Type*} [CommRing R] [Nontrivial R] (x : ℕ) (e : ℕ →₀ ℕ) (c : R)
    (he : e x = 0) :
    mpolyToMpolyPoly x (MvPolynomial.monomial e c) = Polynomial.C (MvPolynomial.monomial e c) := by
  unfold mpolyToMpolyPoly
  rw [MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq, map_mul, RingHom.comp_apply,
    Finsupp.prod, Finsupp.prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hjx : j ≠ x := by
    rintro rfl; exact (Finsupp.mem_support_iff.1 hj) he
  rw [if_neg hjx, map_pow]

theorem g62s_partB {R : Type*} [CommRing R] [Nontrivial R] (x k : ℕ) :
    mpolyToMpolyPoly x (MvPolynomial.monomial (Finsupp.single x k) (1 : R)) = Polynomial.X ^ k := by
  unfold mpolyToMpolyPoly
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_single_index (by simp)]
  simp

theorem g62s_mono {R : Type*} [CommRing R] [Nontrivial R] (x : ℕ) (d : ℕ →₀ ℕ) (c : R) :
    mpolyToMpolyPoly x (MvPolynomial.monomial d c) =
      Polynomial.monomial (d x) (MvPolynomial.monomial (d.erase x) c) := by
  have hd : MvPolynomial.monomial d c =
      MvPolynomial.monomial (d.erase x) c * MvPolynomial.monomial (Finsupp.single x (d x)) (1 : R) := by
    rw [MvPolynomial.monomial_mul, mul_one, Finsupp.erase_add_single]
  have hmul : ∀ a b : MvPolynomial ℕ R, mpolyToMpolyPoly x (a * b) = mpolyToMpolyPoly x a * mpolyToMpolyPoly x b :=
    fun a b => map_mul _ a b
  rw [hd, hmul, g62s_partA x _ c (by simp), g62s_partB, Polynomial.C_mul_X_pow_eq_monomial]

theorem solution {R : Type*} [CommRing R] [Nontrivial R]
    (x : ℕ) (p : MvPolynomial ℕ R) :
    mpolyToMpolyPolyAlt x p = mpolyToMpolyPoly x p := by
  classical
  have hadd : ∀ (s : Finset (ℕ →₀ ℕ)) (f : (ℕ →₀ ℕ) → MvPolynomial ℕ R),
      mpolyToMpolyPoly x (∑ d ∈ s, f d) = ∑ d ∈ s, mpolyToMpolyPoly x (f d) :=
    fun s f => map_sum _ f s
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [hadd]
  simp_rw [g62s_mono]
  unfold mpolyToMpolyPolyAlt isolateVariableSparse
  simp_rw [map_sum, apply_ite (Polynomial.monomial _), map_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le (MvPolynomial.monomial_le_degreeOf x hd)))]
