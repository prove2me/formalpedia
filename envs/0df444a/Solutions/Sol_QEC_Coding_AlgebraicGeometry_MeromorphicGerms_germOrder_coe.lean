-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.germOrder_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:03:00.311245+00:00
-- url     : https://prove2.me/submissions/757d68fb-3668-4142-bfae-fc817e3160ed

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
theorem _root_.solution (x : ℂ) (f : ℂ → ℂ) :
    germOrder x (f : Germ (𝓝[≠] x) ℂ) = meromorphicOrderAt f x := rfl
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
