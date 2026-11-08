-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspNumerator_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:21:43.145202+00:00
-- url     : https://prove2.me/submissions/841cfad8-6e93-4386-8840-b8eff3882f74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspNumerator_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspNumerator_shifted_taylor

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (B : ℕ) (x : LPSOriginalCuspIndex N) :
    PowerSeries.map (lpsOriginalLevelPhaseRing N).val
      (PowerSeries.X^(B-(lpsOriginalCosetCuspData N hN x).1) *
        lpsOriginalPhaseCuspNumerator (lpsOriginalLevelPhaseRing N) N
          (lpsOriginalCosetCuspData N hN x).1
          (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
          (lpsOriginalCosetPhaseElement N hN x)) =
      lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp B
        (lpsOriginalCosetCuspWitness N hN x).1.val
        (lpsOriginalCosetCuspWitness N hN x).2.val) := by
  rw [map_mul,map_pow,PowerSeries.map_X,
    lpsOriginalPhaseCuspNumerator_map]
  exact lpsOriginalPhaseCuspNumerator_shifted_taylor N hN B _ _ _
    (lpsOriginalCosetCuspWitness N hN x).2.property.2.1
end QEC.Coding.TannerLiftedProduct
