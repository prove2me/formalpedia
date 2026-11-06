-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegativeOrder_iff_analytic_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:25.93899+00:00
-- url     : https://prove2.me/submissions/b45fefee-02b7-48fc-931a-5f1be724e06c

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
theorem _root_.solution (x : ℂ) (f : ℂ → ℂ)
    (hf : MeromorphicAt f x) :
    0 ≤ meromorphicOrderValuation x ⟨(f : Germ (𝓝[≠] x) ℂ),f,hf,rfl⟩ ↔
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ f =ᶠ[𝓝[≠] x] g :=
  hf.meromorphicOrderAt_nonneg_iff
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
