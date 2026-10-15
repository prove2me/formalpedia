-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.joined_product
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:50:10.905869+00:00
-- url     : https://prove2.me/submissions/577b056a-5f08-4e79-b585-0e26bb297ef3

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba

section


/-!
# Dense integer Karatsuba multiplication

This file implements a dense, low-coefficient-first list algorithm. Its
correctness theorem is an equality of integer polynomials. The instrumented
work model counts list traversal and scalar arithmetic primitives; it is a
separate obligation to compile this implementation to `Light` and prove the
benchmark's word-RAM step and word-size bounds.
-/

namespace ThreeSum.Karatsuba

open Polynomial
















@[simp] theorem length_plus (as bs : List ℤ) :
    (plus as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [plus]
  | cons a as ih =>
    cases bs with
    | nil => simp [plus]
    | cons b bs => simpa [plus, Nat.succ_max_succ] using congrArg Nat.succ (ih bs)












@[simp] theorem asPolynomial_plus (as bs : List ℤ) :
    asPolynomial (plus as bs) = asPolynomial as + asPolynomial bs := by
  induction as generalizing bs with
  | nil => simp [plus, asPolynomial]
  | cons a as ih =>
    cases bs with
    | nil => simp [plus, asPolynomial]
    | cons b bs =>
      simp only [plus, asPolynomial, ih, map_add]
      ring


























/-- Splitting at a coefficient boundary is exact, also for padded short lists. -/
theorem asPolynomial_split (n : ℕ) (as : List ℤ) :
    asPolynomial as = asPolynomial (as.take n) + X ^ n * asPolynomial (as.drop n) := by
  induction n generalizing as with
  | zero => simp [asPolynomial]
  | succ n ih =>
    cases as with
    | nil => simp [asPolynomial]
    | cons a as =>
      simp only [List.take_succ_cons, List.drop_succ_cons, asPolynomial, pow_succ]
      rw [ih as]
      ring













































































/-! ## Explicit traversal/arithmetic work model

The following charges reflect the operations in the executable list code:
two units per matched coefficient of `plus`; two per mapped coefficient of
`negate`; two per generated/concatenated zero of `shift`; and the two scans
used by `take` and `drop`. The fixed per-call charges include list tests.
They are a conventional unit-cost list/arithmetic model, **not** a theorem
about the benchmark machine or Lean's runtime system.

The recursive charge below uses the actual intermediate list sizes. The
uniform three-subcall recurrence is proved from those sizes; it is not an
assumption that the desired multiplication bound already holds.
-/




















































































end ThreeSum.Karatsuba

end

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



































end ThreeSum.Karatsuba

end

section


/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba

open Light
open ThreeSum.Karatsuba
open Polynomial

























































































































section Join

variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}




































































































































end Join

section BaseCase

variable {lim : Limits} {P : Program} {d : ℕ}






































end BaseCase

@[simp] theorem window_sub (f g : ℕ → ℤ) (offset n j : ℕ) :
    window (fun i => f i - g i) offset n j =
      window f offset n j - window g offset n j := by
  unfold window
  split_ifs <;> simp

theorem ProductAt.window {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (offset j : ℕ) :
    window (fun i => μ (out + i)) offset (2 * n) j =
      (X ^ offset * (asPolynomial as * asPolynomial bs)).coeff j := by
  rw [Polynomial.coeff_X_pow_mul']
  unfold ThreeSum.LightKaratsuba.window
  by_cases ho : offset ≤ j
  · rw [if_pos ho]
    by_cases hj : j < offset + 2 * n
    · rw [if_pos ⟨ho, hj⟩]
      exact hp _ (by omega)
    · rw [if_neg (by omega : ¬ (offset ≤ j ∧ j < offset + 2 * n))]
      exact (product_coeff_zero ha hb (by omega : 2 * n ≤ j - offset)).symm
  · rw [if_neg ho, if_neg (by omega : ¬ (offset ≤ j ∧ j < offset + 2 * n))]

/-- The coefficient identity matched by the six actual joining passes. -/
theorem joined_product_sourceProof {μ : ℕ → ℤ} {work n half : ℕ} {as bs : List ℤ}
    (hhalf : 2 * half = n) (ha : as.length = n) (hb : bs.length = n)
    (h0 : ProductAt μ work half (as.take half) (bs.take half))
    (h2 : ProductAt μ (work + n) half (as.drop half) (bs.drop half))
    (hm : ProductAt μ (work + 2 * n) half
      (plus (as.take half) (as.drop half)) (plus (bs.take half) (bs.drop half)))
    (j : ℕ) : joined μ work n half j = (asPolynomial as * asPolynomial bs).coeff j := by
  have ha0 : (as.take half).length ≤ half := by simp
  have hb0 : (bs.take half).length ≤ half := by simp
  have ha1 : (as.drop half).length ≤ half := by simp only [List.length_drop, ha]; omega
  have hb1 : (bs.drop half).length ≤ half := by simp only [List.length_drop, hb]; omega
  have has : (plus (as.take half) (as.drop half)).length ≤ half := by
    simpa only [length_plus] using max_le ha0 ha1
  have hbs : (plus (bs.take half) (bs.drop half)).length ≤ half := by
    simpa only [length_plus] using max_le hb0 hb1
  have hw0 := h0.window ha0 hb0 0 j
  have hw0m := h0.window ha0 hb0 half j
  have hw2m := h2.window ha1 hb1 half j
  have hw2 := h2.window ha1 hb1 n j
  have hwm := hm.window has hbs half j
  rw [hhalf] at hw0 hw0m hw2m hw2 hwm
  unfold joined
  rw [window_sub, window_sub, hw0, hwm, hw0m, hw2m, hw2]
  simp only [pow_zero, one_mul]
  have hp :
      asPolynomial (as.take half) * asPolynomial (bs.take half) +
        (X ^ half * (asPolynomial (plus (as.take half) (as.drop half)) *
          asPolynomial (plus (bs.take half) (bs.drop half))) -
         X ^ half * (asPolynomial (as.take half) * asPolynomial (bs.take half)) -
         X ^ half * (asPolynomial (as.drop half) * asPolynomial (bs.drop half))) +
        X ^ n * (asPolynomial (as.drop half) * asPolynomial (bs.drop half)) =
      asPolynomial as * asPolynomial bs := by
    rw [asPolynomial_plus, asPolynomial_plus]
    conv_rhs => rw [asPolynomial_split half as, asPolynomial_split half bs]
    rw [← hhalf, two_mul, pow_add]
    ring
  simpa only [Polynomial.coeff_add, Polynomial.coeff_sub] using
    congrArg (fun p : Polynomial ℤ => p.coeff j) hp



















































section RecursiveExecution

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}











































































































































end RecursiveExecution

section CompleteProcedure

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}




















































































end CompleteProcedure

end ThreeSum.LightKaratsuba

end


theorem solution : ∀ {μ : Nat → Int} {work n half : Nat} {as bs : List.{0} Int},
  @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) half)
      n →
    @Eq.{1} Nat (@List.length.{0} Int as) n →
      @Eq.{1} Nat (@List.length.{0} Int bs) n →
        ThreeSum.LightKaratsuba.ProductAt μ work half (@List.take.{0} Int half as) (@List.take.{0} Int half bs) →
          ThreeSum.LightKaratsuba.ProductAt μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work n)
              half (@List.drop.{0} Int half as) (@List.drop.{0} Int half bs) →
            ThreeSum.LightKaratsuba.ProductAt μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                half (ThreeSum.Karatsuba.plus (@List.take.{0} Int half as) (@List.drop.{0} Int half as))
                (ThreeSum.Karatsuba.plus (@List.take.{0} Int half bs) (@List.drop.{0} Int half bs)) →
              ∀ (j : Nat),
                @Eq.{1} Int (ThreeSum.LightKaratsuba.joined μ work n half j)
                  (@Polynomial.coeff.{0} Int Int.instSemiring
                    (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.{0} Int Int.instSemiring)
                      (@Polynomial.{0} Int Int.instSemiring)
                      (@instHMul.{0} (@Polynomial.{0} Int Int.instSemiring)
                        (@Polynomial.instMul.{0} Int Int.instSemiring))
                      (ThreeSum.Karatsuba.asPolynomial as) (ThreeSum.Karatsuba.asPolynomial bs))
                    j) := by
  exact @ThreeSum.LightKaratsuba.joined_product_sourceProof

#print axioms solution
