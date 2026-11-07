-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_integralQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:16.327191+00:00
-- url     : https://prove2.me/submissions/c5e80aea-e27a-4f14-807c-5b5af458eeaa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_annihilatorQ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    IsIntegral (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  obtain ⟨P,hP,_,he⟩ := lpsOriginalJNInFractionField_annihilatorQ N hN
  exact ⟨P,hP,he⟩
end QEC.Coding.TannerLiftedProduct
