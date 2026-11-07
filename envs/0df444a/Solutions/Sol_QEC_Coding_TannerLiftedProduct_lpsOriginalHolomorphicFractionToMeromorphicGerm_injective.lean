-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFractionToMeromorphicGerm_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:14:38.620858+00:00
-- url     : https://prove2.me/submissions/556e5495-4a7a-41dc-b1b9-a4a6d039360a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Algebra.Field.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective lpsOriginalHolomorphicFractionToMeromorphicGerm :=
  lpsOriginalHolomorphicFractionToMeromorphicGerm.injective
end QEC.Coding.TannerLiftedProduct
