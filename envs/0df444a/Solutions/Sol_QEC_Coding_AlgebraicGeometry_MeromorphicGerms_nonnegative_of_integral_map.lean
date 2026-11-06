-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegative_of_integral_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:26.872583+00:00
-- url     : https://prove2.me/submissions/bac33143-81c5-45cc-94b7-2f898e83bcaa

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Polynomial.AlgebraMap
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_valuation_le_one_of_integral_map

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution
    {R A : Type*} [CommRing R] [CommRing A]
    (v : AddValuation A (WithTop ℤ)) (f : R →+* A)
    (hf : ∀ r, 0 ≤ v (f r)) {a : A} (ha : f.IsIntegralElem a) :
    0 ≤ v a := by
  exact valuation_le_one_of_integral_map (AddValuation.toValuation v) f hf ha
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
