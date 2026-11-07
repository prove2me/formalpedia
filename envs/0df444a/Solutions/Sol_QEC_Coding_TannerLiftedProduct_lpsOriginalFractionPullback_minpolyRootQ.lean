-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFractionPullback_minpolyRootQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:09:08.735856+00:00
-- url     : https://prove2.me/submissions/46cd174d-42d6-4d3f-9c6e-4ef01f1303d3

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
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval
      (lpsOriginalFractionPullbackQ g (lpsOriginalJNInFractionField N hN))
      (minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN))=0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact minpoly.aeval_algHom (FractionRing (Polynomial ℚ))
    (lpsOriginalFractionPullbackQ g).toAlgHom
    (lpsOriginalJNInFractionField N hN)
end QEC.Coding.TannerLiftedProduct
