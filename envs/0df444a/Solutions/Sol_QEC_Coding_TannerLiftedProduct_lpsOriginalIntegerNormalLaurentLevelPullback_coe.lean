-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLaurentLevelPullback_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:57:03.35285+00:00
-- url     : https://prove2.me/submissions/504c9da5-11b9-4647-9d6f-5b78853f5d32

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
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalIntegerNormalLaurentChart N hN) :
    (((lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM x :
      lpsOriginalIntegerNormalLaurentChart M hM) :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      ((x : lpsOriginalGeneratedFunctionFieldQ N hN) :
        LPSOriginalHolomorphicFractionField) := by
  exact lpsOriginalRationalLevelInclusion_coe N M hNM h4N hN hM
    (x : lpsOriginalGeneratedFunctionFieldQ N hN)
end QEC.Coding.TannerLiftedProduct
