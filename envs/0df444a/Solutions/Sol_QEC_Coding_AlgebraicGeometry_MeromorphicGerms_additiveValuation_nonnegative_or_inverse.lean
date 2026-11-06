-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.additiveValuation_nonnegative_or_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:28.746876+00:00
-- url     : https://prove2.me/submissions/1b56fe55-81ac-4237-98de-74730da46183

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
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (a : K) :
    0 ≤ v a ∨ 0 ≤ v a⁻¹ := by
  rw [v.map_inv]
  induction v a using WithTop.recTopCoe with
  | top => exact Or.inl le_top
  | coe n =>
      rcases le_total 0 n with hn | hn
      · left; exact_mod_cast hn
      · right
        rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
        exact_mod_cast (neg_nonneg.mpr hn)
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
