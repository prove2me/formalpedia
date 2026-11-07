-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFractionPullback_minpolyRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:19:06.926682+00:00
-- url     : https://prove2.me/submissions/5abcf2ab-04ce-4b1c-b7ec-df95fdf0caf9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 0<N) (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Polynomial.aeval
      (lpsOriginalFractionPullback g (lpsOriginalJNInFractionField N hN))
      (minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN))=0 := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact minpoly.aeval_algHom (FractionRing (Polynomial ℂ))
    (lpsOriginalFractionPullback g).toAlgHom
    (lpsOriginalJNInFractionField N hN)
end QEC.Coding.TannerLiftedProduct
