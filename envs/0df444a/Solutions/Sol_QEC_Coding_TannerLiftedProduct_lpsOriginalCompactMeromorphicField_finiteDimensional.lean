-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicField_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:17:59.842677+00:00
-- url     : https://prove2.me/submissions/ed40ae4a-0f1f-40c2-a4dc-fbb71481bf6f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    FiniteDimensional (FractionRing (Polynomial ℂ))
      (LPSOriginalCompactMeromorphicGermRing N hN) := by
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
  let e := lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
end QEC.Coding.TannerLiftedProduct
