-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.valuation_le_one_of_integral_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:01:33.793506+00:00
-- url     : https://prove2.me/submissions/d18c78ca-8a53-456a-a9db-7bdb10a0306e

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
    {R A Γ : Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation A Γ) (f : R →+* A) (hf : ∀ r, v (f r) ≤ 1)
    {a : A} (ha : f.IsIntegralElem a) : v a ≤ 1 := by
  let g : R →+* v.integer := f.codRestrict v.integer hf
  have h : (v.integer.subtype.comp g).IsIntegralElem a := ha
  have hi : IsIntegral v.integer a := h.of_comp
  exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hi
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
