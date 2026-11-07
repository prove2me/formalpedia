-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionEmbeddingQ_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:57:57.843219+00:00
-- url     : https://prove2.me/submissions/a7633a58-b2b1-492c-91d4-1a954a17d002

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (P : Polynomial ℚ) :
    lpsOriginalJFractionEmbeddingQ (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)=
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEvalQ P) :=
  IsFractionRing.lift_algebraMap _ P
end QEC.Coding.TannerLiftedProduct
