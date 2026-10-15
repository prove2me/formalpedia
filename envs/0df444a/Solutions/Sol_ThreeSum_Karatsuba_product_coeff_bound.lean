-- Prove2me | solution 1 for ThreeSum.Karatsuba.product_coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:32.276915+00:00
-- url     : https://prove2.me/submissions/93253f3b-5a95-4181-9bb2-2c8554eb4806

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-! # Coefficient and intermediate-value bounds for the array realization -/

namespace ThreeSum.Karatsuba

open Polynomial
open scoped BigOperators

@[simp] theorem asPolynomial_coeff (as : List ℤ) (j : ℕ) :
    (asPolynomial as).coeff j = as.getD j 0 := by
  induction as generalizing j with
  | nil => simp [asPolynomial]
  | cons a as ih =>
    cases j with
    | zero => simp [asPolynomial]
    | succ j =>
      rw [asPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul, ih]
      simp













theorem coeffBound_nonneg {as : List ℤ} {U : ℤ} (h : CoeffBound as U) : 0 ≤ U :=
  (abs_nonneg _).trans (h 0)



































theorem product_coeff_zero {as bs : List ℤ} {n j : ℕ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n) (hj : 2 * n ≤ j) :
    (asPolynomial as * asPolynomial bs).coeff j = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  by_cases hpa : n ≤ p.1
  · rw [asPolynomial_coeff, List.getD_eq_default _ _ (ha.trans hpa), zero_mul]
  · have hpb : n ≤ p.2 := by omega
    rw [asPolynomial_coeff bs, List.getD_eq_default _ _ (hb.trans hpb), mul_zero]

/-- All true product coefficients have a polynomial value bound, including
the implicit zeros outside the stored output. -/
theorem product_coeff_bound_sourceProof {as bs : List ℤ} {n : ℕ} {U : ℤ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) (j : ℕ) :
    |(asPolynomial as * asPolynomial bs).coeff j| ≤ 2 * (n : ℤ) * U ^ 2 := by
  have hU : 0 ≤ U := coeffBound_nonneg hA
  by_cases hj : 2 * n ≤ j
  · rw [product_coeff_zero ha hb hj, abs_zero]
    positivity
  · have hj' : j + 1 ≤ 2 * n := by omega
    rw [Polynomial.coeff_mul]
    calc
      _ ≤ ∑ p ∈ Finset.antidiagonal j,
          |(asPolynomial as).coeff p.1 * (asPolynomial bs).coeff p.2| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _p ∈ Finset.antidiagonal j, U ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul, asPolynomial_coeff, asPolynomial_coeff, pow_two]
        exact mul_le_mul (hA p.1) (hB p.2) (abs_nonneg _) hU
      _ = (j + 1 : ℕ) * U ^ 2 := by simp
      _ ≤ 2 * (n : ℤ) * U ^ 2 := by
        have hjR : (j + 1 : ℕ) ≤ (2 * (n : ℤ)) := by exact_mod_cast hj'
        exact mul_le_mul_of_nonneg_right hjR (sq_nonneg U)









end ThreeSum.Karatsuba

end


theorem solution : ∀ {as bs : List.{0} Int} {n : Nat} {U : Int},
  @LE.le.{0} Nat instLENat (@List.length.{0} Int as) n →
    @LE.le.{0} Nat instLENat (@List.length.{0} Int bs) n →
      ThreeSum.Karatsuba.CoeffBound as U →
        ThreeSum.Karatsuba.CoeffBound bs U →
          ∀ (j : Nat),
            @LE.le.{0} Int Int.instLEInt
              (@abs.{0} Int instLatticeInt Int.instAddGroup
                (@Polynomial.coeff.{0} Int Int.instSemiring
                  (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.{0} Int Int.instSemiring)
                    (@Polynomial.{0} Int Int.instSemiring)
                    (@instHMul.{0} (@Polynomial.{0} Int Int.instSemiring)
                      (@Polynomial.instMul.{0} Int Int.instSemiring))
                    (ThreeSum.Karatsuba.asPolynomial as) (ThreeSum.Karatsuba.asPolynomial bs))
                  j))
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                  (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@Nat.cast.{0} Int instNatCastInt n))
                (@HPow.hPow.{0, 0, 0} Int Nat Int
                  (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) U
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  exact @ThreeSum.Karatsuba.product_coeff_bound_sourceProof

#print axioms solution
