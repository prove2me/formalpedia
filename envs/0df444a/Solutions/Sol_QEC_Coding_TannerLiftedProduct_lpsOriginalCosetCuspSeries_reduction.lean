-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspSeries_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:41:44.904901+00:00
-- url     : https://prove2.me/submissions/3ff29dbd-7643-43ed-bd83-382b3aae9898

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_map

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspCoefficientMap
      (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp))
      (lpsOriginalCosetIntegralCuspSeries N hN x) =
        lpsOriginalCosetResidueCuspSeries N hN p hp x :=
  lpsOriginalPhaseCuspSeries_map _ _ _ N _ _ _
end QEC.Coding.TannerLiftedProduct
