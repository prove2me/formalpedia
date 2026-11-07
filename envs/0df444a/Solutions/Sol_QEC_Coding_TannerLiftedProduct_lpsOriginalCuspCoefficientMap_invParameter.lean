-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_invParameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:18:11.814115+00:00
-- url     : https://prove2.me/submissions/fcddf4b1-a874-4685-afd0-c154844cf312

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_series

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) :
    lpsOriginalCuspCoefficientMap f
      (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))=
      IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing S)
        (PowerSeries.X : PowerSeries S) := by
  have h:=congrArg (lpsOriginalCuspCoefficientMap f)
    (IsLocalization.Away.mul_invSelf (S:=lpsOriginalCuspSeriesRing R)
      (PowerSeries.X : PowerSeries R))
  rw [map_mul,map_one,lpsOriginalCuspCoefficientMap_series,PowerSeries.map_X] at h
  exact (IsLocalization.Away.algebraMap_isUnit (S:=lpsOriginalCuspSeriesRing S)
    (PowerSeries.X : PowerSeries S)).mul_left_cancel
      (h.trans (IsLocalization.Away.mul_invSelf (S:=lpsOriginalCuspSeriesRing S)
        (PowerSeries.X : PowerSeries S)).symm)
end QEC.Coding.TannerLiftedProduct
