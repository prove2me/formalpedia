-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicDeltaQCoefficient_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:32:46.134739+00:00
-- url     : https://prove2.me/submissions/9302df8f-a7a1-47e7-a8fb-8ffa85c10077

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    AnalyticAt ℂ lpsOriginalMeromorphicDeltaQCoefficient 0 := by
  have hD := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  obtain ⟨P,hP⟩ := hD
  exact ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
end QEC.Coding.TannerLiftedProduct
