-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalLevelInclusion_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:12:31.969653+00:00
-- url     : https://prove2.me/submissions/8d474b73-ecf6-4221-ac27-f8e8e7d75bb7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    ((lpsOriginalRationalLevelInclusion N M hNM h4N hN hM x :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      (x : LPSOriginalHolomorphicFractionField) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact IntermediateField.coe_inclusion
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM h4N hN hM) x
end QEC.Coding.TannerLiftedProduct
