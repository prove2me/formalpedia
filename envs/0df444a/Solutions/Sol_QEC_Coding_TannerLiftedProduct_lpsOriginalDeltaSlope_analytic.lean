-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaSlope_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:43:12.922349+00:00
-- url     : https://prove2.me/submissions/a059039c-b94c-46eb-833d-70634825988d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    AnalyticAt ℂ (dslope (cuspFunction 1 ModularForm.discriminant) 0) 0 := by
  have h := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL
  exact h.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
end QEC.Coding.TannerLiftedProduct
