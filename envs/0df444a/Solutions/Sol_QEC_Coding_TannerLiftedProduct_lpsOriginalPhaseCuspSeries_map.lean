-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:19:23.50065+00:00
-- url     : https://prove2.me/submissions/6fa1b9ba-0ecb-4ca1-aa34-d6ef54e754ec

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspNumerator_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_invParameter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_series


set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S)
    (N m : ℕ) (hm : m ≠ 0) (ζ : R) :
    lpsOriginalCuspCoefficientMap f (lpsOriginalPhaseCuspSeries R N m hm ζ) =
      lpsOriginalPhaseCuspSeries S N m hm (f ζ) := by
  rw [lpsOriginalPhaseCuspSeries,map_mul,map_pow,
    lpsOriginalCuspCoefficientMap_invParameter,lpsOriginalCuspCoefficientMap_series,
    lpsOriginalPhaseCuspNumerator_map]
  rfl
end QEC.Coding.TannerLiftedProduct
