-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedComplexSum_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:32:46.11564+00:00
-- url     : https://prove2.me/submissions/e3e3c819-27f8-486a-99f2-acc4abe6d845

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_const_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_sum


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℂ) :
    lpsOriginalTaylorSeries (lpsOriginalFiniteClearedComplexSum M B u v a) =
      ∑ i, PowerSeries.C (a i) * PowerSeries.map (algebraMap ℚ ℂ)
        (lpsOriginalClearedFormalMonomial M hM B (u i) (v i)) := by
  classical
  unfold lpsOriginalFiniteClearedComplexSum
  rw [lpsOriginalTaylorSeries_sum Finset.univ
    (fun i => fun q => a i * lpsOriginalClearedMonomial M B (u i) (v i) q)
    (fun i _hi => analyticAt_const.mul
      (lpsOriginalClearedMonomial_analytic M hM B (u i) (v i)))]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lpsOriginalTaylorSeries_const_mul, lpsOriginalClearedMonomial_taylor M hM]
end QEC.Coding.TannerLiftedProduct
