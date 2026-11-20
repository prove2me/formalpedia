-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:53:42.419602+00:00
-- url     : https://prove2.me/submissions/4bf24cfe-52eb-4460-9c41-086334e3fec6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Injective (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN) := by
  intro x y h
  exact Subtype.ext (congrArg
    (fun z : lpsOriginalIntegerFrickeLocalizedNormalChart N hN => z.val) h)
end QEC.Coding.TannerLiftedProduct
