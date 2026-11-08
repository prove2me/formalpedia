-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_volume_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:05:46.404274+00:00
-- url     : https://prove2.me/submissions/26156bac-29c3-4817-b4a9-807b4ff74e16

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_volume
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_fundamentalDomain_volume_finite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    (volume : Measure ℍ) (lpsGamma0PeterssonDomain N) < ∞ := by
  rw [lpsGamma0PeterssonDomain_volume]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) lpsPetersson_fundamentalDomain_volume_finite
end QEC.Coding.TannerLiftedProduct
