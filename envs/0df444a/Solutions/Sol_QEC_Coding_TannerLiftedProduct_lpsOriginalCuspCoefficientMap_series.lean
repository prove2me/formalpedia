-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:15:23.701063+00:00
-- url     : https://prove2.me/submissions/42544a93-4747-48b3-9e20-4143e6dd44b9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) :
    lpsOriginalCuspCoefficientMap f
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) F)=
      algebraMap (PowerSeries S) (lpsOriginalCuspSeriesRing S) (PowerSeries.map f F) :=
  IsLocalization.Away.lift_eq _ _ _
end QEC.Coding.TannerLiftedProduct
