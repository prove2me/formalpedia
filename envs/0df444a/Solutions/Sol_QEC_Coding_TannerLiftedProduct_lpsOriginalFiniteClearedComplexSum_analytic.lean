-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedComplexSum_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:32:44.596449+00:00
-- url     : https://prove2.me/submissions/6f608125-cdf4-42dc-9c7f-0fdbad1321c9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_analytic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℂ) :
    AnalyticAt ℂ (lpsOriginalFiniteClearedComplexSum M B u v a) 0 := by
  classical
  exact Finset.univ.analyticAt_sum fun i _hi =>
    analyticAt_const.mul (lpsOriginalClearedMonomial_analytic M hM B (u i) (v i))
end QEC.Coding.TannerLiftedProduct
