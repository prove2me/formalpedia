-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroLevelPullback_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:56:42.103453+00:00
-- url     : https://prove2.me/submissions/d0e005cb-277d-45d7-9b4b-f0835991e021

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalLevelInclusion_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalIntegerNormalZeroChart N hN) :
    (((lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM x :
      lpsOriginalIntegerNormalZeroChart M hM) :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      ((x : lpsOriginalGeneratedFunctionFieldQ N hN) :
        LPSOriginalHolomorphicFractionField) := by
  exact lpsOriginalRationalLevelInclusion_coe N M hNM h4N hN hM
    (x : lpsOriginalGeneratedFunctionFieldQ N hN)
end QEC.Coding.TannerLiftedProduct
