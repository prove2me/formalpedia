-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:25.233201+00:00
-- url     : https://prove2.me/submissions/f8b22abc-799a-4950-9f29-60f2a00dd3b7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_series
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspSeriesAlgebraMap_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {R S : Type*}
    [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (lpsOriginalCuspCoefficientMap f) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) _).mpr
  intro A B
  constructor
  · exact congrArg (lpsOriginalCuspCoefficientMap f)
  · intro h
    rw [lpsOriginalCuspCoefficientMap_series,lpsOriginalCuspCoefficientMap_series] at h
    have he:=lpsOriginalCuspSeriesAlgebraMap_injective S h
    have hab:=PowerSeries.map_injective f hf he
    exact congrArg (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)) hab
end QEC.Coding.TannerLiftedProduct
