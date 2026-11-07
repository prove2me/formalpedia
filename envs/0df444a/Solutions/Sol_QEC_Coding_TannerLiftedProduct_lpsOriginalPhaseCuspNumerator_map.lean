-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspNumerator_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:16:54.12502+00:00
-- url     : https://prove2.me/submissions/32111414-36c6-4510-a41e-1ace138f1aed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_integerNumerator


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
    PowerSeries.map f (lpsOriginalPhaseCuspNumerator R N m hm ζ) =
      lpsOriginalPhaseCuspNumerator S N m hm (f ζ) := by
  rw [lpsOriginalPhaseCuspNumerator,map_mul,PowerSeries.map_C,f.map_pow,
    PowerSeries.map_expand,← PowerSeries.rescale_map,
    lpsOriginalCuspCoefficientMap_integerNumerator]
  rfl
end QEC.Coding.TannerLiftedProduct
