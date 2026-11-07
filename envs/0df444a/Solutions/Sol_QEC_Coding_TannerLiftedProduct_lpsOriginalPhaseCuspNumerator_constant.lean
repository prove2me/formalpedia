-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspNumerator_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:53:43.486212+00:00
-- url     : https://prove2.me/submissions/c67450a0-dd9b-47a2-ba38-b028e3ac73d0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspJNumerator_constant

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type*) [CommRing R] (N m : ℕ) (hm : m ≠ 0) (ζ : R) :
    PowerSeries.constantCoeff (lpsOriginalPhaseCuspNumerator R N m hm ζ) =
      ζ^(N-1) := by
  rw [lpsOriginalPhaseCuspNumerator,map_mul,PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_expand,← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_rescale,pow_zero,one_mul,PowerSeries.coeff_zero_eq_constantCoeff,
    lpsOriginalCuspJNumerator_constant,mul_one]
end QEC.Coding.TannerLiftedProduct
