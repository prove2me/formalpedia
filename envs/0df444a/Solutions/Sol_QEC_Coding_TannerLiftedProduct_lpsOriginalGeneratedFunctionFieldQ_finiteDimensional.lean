-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:47.346293+00:00
-- url     : https://prove2.me/submissions/cbbeb1d2-e249-4334-bf32-6f242928c449

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    FiniteDimensional (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact IntermediateField.adjoin.finiteDimensional
    (lpsOriginalJNInFractionField_integralQ N hN)
end QEC.Coding.TannerLiftedProduct
