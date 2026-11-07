-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_jWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:24:14.637648+00:00
-- url     : https://prove2.me/submissions/f676baf3-8ad9-48b7-b330-be7a8485d030

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_series
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_invParameter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_integerNumerator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) (hm : m≠0) :
    lpsOriginalCuspCoefficientMap f (lpsOriginalCuspJWidth R m hm)=
      lpsOriginalCuspJWidth S m hm := by
  rw [lpsOriginalCuspJWidth,map_mul,map_pow,
    lpsOriginalCuspCoefficientMap_invParameter,lpsOriginalCuspCoefficientMap_series,
    PowerSeries.map_expand,lpsOriginalCuspCoefficientMap_integerNumerator]
  rfl
end QEC.Coding.TannerLiftedProduct
