-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspE4_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:45:42.081939+00:00
-- url     : https://prove2.me/submissions/6c75976f-dc48-4f34-b609-8739330e33bd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_cusp_period
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) (ρ : SL(2,ℤ)) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      (lpsOriginalJDilationCuspE4 N hN ρ)) 0 := by
  exact ModularFormClass.analyticAt_cuspFunction_zero
    (lpsOriginalJDilationCuspE4 N hN ρ) (lpsOriginalCuspGroup_width_positive N ρ)
    (lpsOriginalJDilation_cusp_period N hN ρ)
end QEC.Coding.TannerLiftedProduct
