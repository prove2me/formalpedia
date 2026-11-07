-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionEmbedding_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:56:32.069332+00:00
-- url     : https://prove2.me/submissions/caf9bbd8-a3f6-49a0-8528-7883e74a8315

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (P : Polynomial ℂ) :
    lpsOriginalJFractionEmbedding (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P)=
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEval P) :=
  IsFractionRing.lift_algebraMap _ P
end QEC.Coding.TannerLiftedProduct
