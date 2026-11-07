-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicToMeromorphicGerm_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:01:33.723027+00:00
-- url     : https://prove2.me/submissions/14c7e87d-1668-4eb4-a99c-f2cc2aa7a2fb

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
theorem _root_.solution (c : ℂ) :
    lpsOriginalHolomorphicToMeromorphicGerm
      (algebraMap ℂ LPSOriginalHolomorphicRing c) =
      algebraMap ℂ (LPSOriginalMeromorphicGermRing
        UpperHalfPlane.upperHalfPlaneSet) c := rfl
end QEC.Coding.TannerLiftedProduct
