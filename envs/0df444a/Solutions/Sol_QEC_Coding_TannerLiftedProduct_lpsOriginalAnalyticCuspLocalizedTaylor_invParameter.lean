-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_invParameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:29:57.524216+00:00
-- url     : https://prove2.me/submissions/f4bd13dd-dd74-4ab6-aff7-63a02d2ee4c7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_function

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalAnalyticCuspLocalizedTaylor
      (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
        lpsOriginalAnalyticCuspLaurentParameter)=
      IsLocalization.Away.invSelf (S:=lpsOriginalComplexCuspLaurentRing)
        (PowerSeries.X : PowerSeries ℂ) := by
  have h:=congrArg lpsOriginalAnalyticCuspLocalizedTaylor
    (IsLocalization.Away.mul_invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
      lpsOriginalAnalyticCuspLaurentParameter)
  rw [map_mul,map_one,lpsOriginalAnalyticCuspLocalizedTaylor_function,
    lpsOriginalAnalyticCuspLaurentParameter_taylor] at h
  exact (IsLocalization.Away.algebraMap_isUnit (S:=lpsOriginalComplexCuspLaurentRing)
    (PowerSeries.X : PowerSeries ℂ)).mul_left_cancel
      (h.trans (IsLocalization.Away.mul_invSelf (S:=lpsOriginalComplexCuspLaurentRing)
        (PowerSeries.X : PowerSeries ℂ)).symm)
end QEC.Coding.TannerLiftedProduct
