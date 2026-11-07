-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJZSeries_mapQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:43:25.902535+00:00
-- url     : https://prove2.me/submissions/d565bac0-1fbc-490e-b898-67b0c7c2d323

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlopeZSeries_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlopeZSeries_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4ZSeries_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlopeQSeries_constant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalJZSeries=lpsOriginalJQSeries := by
  have hD : lpsOriginalDeltaSlopeQSeries≠0 := by
    intro h
    have h0:=congrArg PowerSeries.constantCoeff h
    rw [lpsOriginalDeltaSlopeQSeries_constant,map_zero] at h0
    exact one_ne_zero h0
  apply mul_left_cancel₀ hD
  have hL : lpsOriginalDeltaSlopeQSeries*
      PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalJZSeries=(lpsOriginalEisensteinQSeries 4)^3 := by
    rw [←lpsOriginalDeltaSlopeZSeries_map,lpsOriginalJZSeries,←map_mul]
    rw [mul_left_comm,PowerSeries.mul_invOfUnit _ 1 lpsOriginalDeltaSlopeZSeries_constant,
      mul_one,map_pow,lpsOriginalE4ZSeries_map]
  have hR : lpsOriginalDeltaSlopeQSeries*lpsOriginalJQSeries=(lpsOriginalEisensteinQSeries 4)^3 := by
    unfold lpsOriginalJQSeries
    rw [mul_left_comm,PowerSeries.mul_invOfUnit _ 1 lpsOriginalDeltaSlopeQSeries_constant,mul_one]
  exact hL.trans hR.symm
end QEC.Coding.TannerLiftedProduct
