-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegative_laurent_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:29.983924+00:00
-- url     : https://prove2.me/submissions/74f75d6e-c041-4d17-ba49-eefb8cf916ef

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Polynomial.AlgebraMap
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution
    {R A : Type*} [CommRing R] [CommRing A]
    (v : AddValuation A (WithTop ℤ)) (f : LaurentPolynomial R →+* A)
    (hc : ∀ c, 0 ≤ v (f (LaurentPolynomial.C c)))
    (h1 : 0 ≤ v (f (LaurentPolynomial.T 1)))
    (hinv : 0 ≤ v (f (LaurentPolynomial.T (-1)))) (p : LaurentPolynomial R) :
    0 ≤ v (f p) := by
  refine LaurentPolynomial.induction_on p hc ?_ ?_ ?_
  · intro p q hp hq
    rw [map_add]
    exact v.map_le_add hp hq
  · intro n c hn
    have he : LaurentPolynomial.C c * LaurentPolynomial.T ((n : ℤ)+1) =
        (LaurentPolynomial.C c * LaurentPolynomial.T (n : ℤ)) * LaurentPolynomial.T 1 := by
      rw [mul_assoc, ← LaurentPolynomial.T_add]
    rw [he, map_mul, v.map_mul]
    exact add_nonneg hn h1
  · intro n c hn
    have he : LaurentPolynomial.C c * LaurentPolynomial.T (-(n : ℤ)-1) =
        (LaurentPolynomial.C c * LaurentPolynomial.T (-(n : ℤ))) *
          LaurentPolynomial.T (-1) := by
      rw [mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg]
    rw [he, map_mul, v.map_mul]
    exact add_nonneg hn hinv
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
