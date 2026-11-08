-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicField_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:18:24.426525+00:00
-- url     : https://prove2.me/submissions/7652e8b5-8447-48dd-b6ca-f1964131c6fc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finrank_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ))
      (LPSOriginalCompactMeromorphicGermRing N hN) =
        Nat.card (LPSOriginalMeromorphicCosets N) := by
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [←(lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN).toLinearEquiv.finrank_eq]
  exact lpsOriginalGeneratedFunctionField_finrank_eq N hpos
end QEC.Coding.TannerLiftedProduct
