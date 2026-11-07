-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_taylor_ne_zero_of_original_denominator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:31:49.155096+00:00
-- url     : https://prove2.me/submissions/8fae8142-2e43-4f3c-a12a-b4304d2fb1ea

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_pullback_of_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphic_zero_of_clearedNomeGerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalBivariateHolomorphicEval_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero_iff_germ


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (M : ℕ) (hM : 0 < M) (B : ℕ) (P : Polynomial (Polynomial ℂ))
    (hB : lpsOriginalClearingBound M P ≤ B)
    (hP : lpsOriginalBivariateHolomorphicEval M hM P ≠ 0) :
    lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B P) ≠ 0 := by
  intro hz
  have hg : lpsOriginalClearedCusp M B P =ᶠ[𝓝 (0 : ℂ)] 0 :=
    (lpsOriginalTaylorSeries_zero_iff_germ
      (lpsOriginalClearedCusp_analytic M (Nat.ne_of_gt hM) B P)).mp hz
  apply hP
  apply lpsOriginalHolomorphic_zero_of_clearedNomeGerm
    (lpsOriginalBivariateHolomorphicEval M hM P)
    (lpsOriginalClearedCusp M B P) B hg
  intro τ
  rw [lpsOriginalBivariateHolomorphicEval_apply]
  exact lpsOriginalClearedCusp_pullback_of_bound M hM B P hB τ
end QEC.Coding.TannerLiftedProduct
