-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedSecondLevelMap_overSpecZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:00:25.306182+00:00
-- url     : https://prove2.me/submissions/3285ab30-4256-4dc3-9253-122899f09221

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSpecZ_hom_unique


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToSpecZ N hN = lpsOriginalIntegerNormalGluedToSpecZ M hM := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let := lpsOriginalIntegerNormalGeneratedFieldPoint_dominant M hM
  apply ext_of_isDominant (lpsOriginalIntegerNormalGeneratedFieldPoint M hM)
  exact lpsOriginalIntegerSpecZ_hom_unique (lpsOriginalGeneratedFunctionFieldQ M hM) _ _
end QEC.Coding.TannerLiftedProduct
