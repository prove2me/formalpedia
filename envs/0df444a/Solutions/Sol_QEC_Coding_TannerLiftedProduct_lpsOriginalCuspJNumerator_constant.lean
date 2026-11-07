-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspJNumerator_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:50:44.069911+00:00
-- url     : https://prove2.me/submissions/d6cdcf7a-e72e-44af-a7f9-b1a70bf1a71c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJZSeries_constant


set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (R : Type*) [CommRing R] :
    PowerSeries.constantCoeff (lpsOriginalCuspJNumerator R) = 1 := by
  rw [lpsOriginalCuspJNumerator, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff,
    lpsOriginalJZSeries_constant,map_one]
end QEC.Coding.TannerLiftedProduct
