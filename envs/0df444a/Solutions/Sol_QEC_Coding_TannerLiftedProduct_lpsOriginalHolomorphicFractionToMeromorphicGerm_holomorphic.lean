-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:58:42.5452+00:00
-- url     : https://prove2.me/submissions/1ba7b5d7-29b4-47b7-94cf-644c7d57f068

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
theorem _root_.solution
    (f : LPSOriginalHolomorphicRing) :
    lpsOriginalHolomorphicFractionToMeromorphicGerm
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField f) =
      lpsOriginalHolomorphicToMeromorphicGerm f :=
  IsFractionRing.lift_algebraMap _ f
end QEC.Coding.TannerLiftedProduct
