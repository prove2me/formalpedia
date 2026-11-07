-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetResiduePhase_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:41:46.306407+00:00
-- url     : https://prove2.me/submissions/dc72d59b-67a3-404d-bacc-d582c3a66970

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetPhaseElement_pow


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
    (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp)
      (lpsOriginalCosetPhaseElement N hN x))^N = 1 := by
  rw [← map_pow,lpsOriginalCosetPhaseElement_pow,map_one]
end QEC.Coding.TannerLiftedProduct
