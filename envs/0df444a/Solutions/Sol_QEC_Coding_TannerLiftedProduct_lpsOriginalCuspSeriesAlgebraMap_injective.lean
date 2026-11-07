-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspSeriesAlgebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:15:24.981397+00:00
-- url     : https://prove2.me/submissions/1f0551a4-b127-4306-8063-c7383f79304b

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
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] :
    Function.Injective (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)) := by
  apply IsLocalization.injective (M:=Submonoid.powers (PowerSeries.X : PowerSeries R))
  intro x hx
  obtain ⟨n,rfl⟩:=hx
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n PowerSeries.X_ne_zero)
end QEC.Coding.TannerLiftedProduct
