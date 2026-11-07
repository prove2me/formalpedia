-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:08:01.384199+00:00
-- url     : https://prove2.me/submissions/9721b46d-484e-47c8-a28e-386a50c918f0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_toJ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_finite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM) := by
  let := lpsOriginalIntegerNormalGluedToProjectiveJ_finite N hN
  let := lpsOriginalIntegerNormalGluedToProjectiveJ_finite M hM
  let : IsFinite (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN) := by
    rw [lpsOriginalIntegerNormalGluedForgetLevel_toJ]
    infer_instance
  exact IsFinite.of_comp (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM)
    (lpsOriginalIntegerNormalGluedToProjectiveJ N hN)
end QEC.Coding.TannerLiftedProduct
