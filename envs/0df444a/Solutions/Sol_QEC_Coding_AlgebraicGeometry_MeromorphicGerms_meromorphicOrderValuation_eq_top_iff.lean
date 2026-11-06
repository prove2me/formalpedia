-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicOrderValuation_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:25.039874+00:00
-- url     : https://prove2.me/submissions/9819e2ee-246c-46e8-9de3-61807462e3e2

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Polynomial.AlgebraMap
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germOrder_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution (x : ℂ) (A : MeromorphicGermRing x) :
    meromorphicOrderValuation x A = ⊤ ↔ A = 0 := by
  obtain ⟨f,hf,he⟩ := A.property
  change germOrder x A.val = ⊤ ↔ A = 0
  rw [he, germOrder_coe, meromorphicOrderAt_eq_top_iff]
  constructor
  · intro h
    apply Subtype.ext
    rw [he]
    exact Filter.Germ.coe_eq.mpr h
  · intro h
    have hv : (f : Germ (𝓝[≠] x) ℂ) = 0 := by
      rw [← he]
      exact congrArg Subtype.val h
    exact Filter.Germ.coe_eq.mp hv
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
