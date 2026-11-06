-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegative_polynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:27.737227+00:00
-- url     : https://prove2.me/submissions/e0fa93d8-cddf-4718-a4f9-f8bdd3a330a1

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
    (v : AddValuation A (WithTop ℤ)) (f : R →+* A)
    (hf : ∀ r, 0 ≤ v (f r)) (a : A) (ha : 0 ≤ v a) (p : Polynomial R) :
    0 ≤ v (p.eval₂ f a) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add]
      exact v.map_le_add hp hq
  | monomial n c =>
      rw [Polynomial.eval₂_monomial, v.map_mul, v.map_pow]
      exact add_nonneg (hf c) (nsmul_nonneg ha n)
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
