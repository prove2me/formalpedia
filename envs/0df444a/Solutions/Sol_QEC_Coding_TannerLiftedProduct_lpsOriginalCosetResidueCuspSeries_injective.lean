-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetResidueCuspSeries_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:14:18.622672+00:00
-- url     : https://prove2.me/submissions/a9210dce-d64c-4fac-a045-020083b9f660

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_equalData
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetResiduePhase_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetCuspResidueData_injective


set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Function.Injective (lpsOriginalCosetResidueCuspSeries N hN p hp) := by
  intro x y hxy
  have hd := lpsOriginalPhaseCuspSeries_equalData
    (LPSOriginalLevelPhaseResidue N hN p hp) N hN
    (lpsOriginalCosetCuspData N hN x).1
    (lpsOriginalCosetCuspData N hN y).1
    (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
    (lpsOriginalCosetCuspData_slope_pos N hN y).ne'
    _ _ (lpsOriginalCosetResiduePhase_pow N hN p hp x)
    (lpsOriginalCosetResiduePhase_pow N hN p hp y) hxy
  apply lpsOriginalCosetCuspResidueData_injective N hN p hp hpN
  exact Prod.ext hd.1 hd.2
end QEC.Coding.TannerLiftedProduct
