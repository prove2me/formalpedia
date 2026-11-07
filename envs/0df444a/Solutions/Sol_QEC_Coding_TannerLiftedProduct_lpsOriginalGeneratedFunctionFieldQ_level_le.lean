-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:53:37.32191+00:00
-- url     : https://prove2.me/submissions/71bdd8ed-411e-4d77-bf40-fd320cd5944c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_mem_Q_of_mem_complex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_level_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hposN ≤
      lpsOriginalGeneratedFunctionFieldQ M hposM := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change IntermediateField.adjoin (FractionRing (Polynomial ℚ))
    {lpsOriginalJNInFractionField N hposN} ≤ _
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  have he := Set.mem_singleton_iff.mp hx
  subst x
  apply lpsOriginalJNInFractionField_mem_Q_of_mem_complex N M hposN hposM
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact lpsOriginalGeneratedFunctionField_level_le N M hNM hN hposN hposM
    (IntermediateField.subset_adjoin (FractionRing (Polynomial ℂ)) _
      (Set.mem_singleton _))
end QEC.Coding.TannerLiftedProduct
