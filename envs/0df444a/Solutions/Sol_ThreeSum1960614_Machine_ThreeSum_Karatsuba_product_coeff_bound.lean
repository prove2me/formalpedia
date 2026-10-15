-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:21:25.741971+00:00
-- url     : https://prove2.me/submissions/e3dce8aa-6067-4b6b-b6cf-150681e0db1d

import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba

namespace ThreeSum1960614.Machine

/-! # Coefficient and intermediate-value bounds for the array realization -/

namespace ThreeSum.Karatsuba
open _root_.ThreeSum.Karatsuba


open _root_.Polynomial
open scoped _root_.BigOperators

@[simp] theorem asPolynomial_coeff (as : List ℤ) (j : ℕ) :
    (_root_.ThreeSum.Karatsuba.asPolynomial as).coeff j = as.getD j 0 := by
  induction as generalizing j with
  | nil => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
  | cons a as ih =>
    cases j with
    | zero => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
    | succ j =>
      rw [_root_.ThreeSum.Karatsuba.asPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul, ih]
      simp







theorem coeffBound_nonneg {as : List ℤ} {U : ℤ} (h : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) : 0 ≤ U :=
  (abs_nonneg _).trans (h 0)













theorem product_coeff_zero {as bs : List ℤ} {n j : ℕ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n) (hj : 2 * n ≤ j) :
    (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff j = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := _root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases hpa : n ≤ p.1
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff, List.getD_eq_default _ _ (ha.trans hpa), zero_mul]
  · have hpb : n ≤ p.2 := by omega
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff bs, List.getD_eq_default _ _ (hb.trans hpb), mul_zero]





end ThreeSum.Karatsuba

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba

open _root_.Polynomial
open scoped _root_.BigOperators
section

/-- All true product coefficients have a polynomial value bound, including
the implicit zeros outside the stored output. -/
theorem ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_bound__implementation_653f5bc3f1 {as bs : List ℤ} {n : ℕ} {U : ℤ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs U) (j : ℕ) :
    |(_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff j| ≤ 2 * (n : ℤ) * U ^ 2 := by
  have hU : 0 ≤ U := _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.coeffBound_nonneg hA
  by_cases hj : 2 * n ≤ j
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_zero ha hb hj, abs_zero]
    positivity
  · have hj' : j + 1 ≤ 2 * n := by omega
    rw [Polynomial.coeff_mul]
    calc
      _ ≤ ∑ p ∈ _root_.Finset.HasAntidiagonal.antidiagonal j,
          |(_root_.ThreeSum.Karatsuba.asPolynomial as).coeff p.1 * (_root_.ThreeSum.Karatsuba.asPolynomial bs).coeff p.2| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _p ∈ _root_.Finset.HasAntidiagonal.antidiagonal j, U ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff, _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff, pow_two]
        exact mul_le_mul (hA p.1) (hB p.2) (abs_nonneg _) hU
      _ = (j + 1 : ℕ) * U ^ 2 := by simp
      _ ≤ 2 * (n : ℤ) * U ^ 2 := by
        have hjR : (j + 1 : ℕ) ≤ (2 * (n : ℤ)) := by exact_mod_cast hj'
        exact mul_le_mul_of_nonneg_right hjR (sq_nonneg U)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_bound__implementation_653f5bc3f1) := (@ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_bound__implementation_653f5bc3f1)

#print axioms solution
