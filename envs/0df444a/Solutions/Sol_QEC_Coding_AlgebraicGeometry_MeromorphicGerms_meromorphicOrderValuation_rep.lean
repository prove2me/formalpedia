-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicOrderValuation_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:24.120814+00:00
-- url     : https://prove2.me/submissions/6f7f6212-f5ad-406e-be77-c90e2a1b8072

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
theorem _root_.solution (x : ℂ) (f : ℂ → ℂ) (hf : MeromorphicAt f x) :
    meromorphicOrderValuation x ⟨(f : Germ (𝓝[≠] x) ℂ),f,hf,rfl⟩ =
      meromorphicOrderAt f x := rfl
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
