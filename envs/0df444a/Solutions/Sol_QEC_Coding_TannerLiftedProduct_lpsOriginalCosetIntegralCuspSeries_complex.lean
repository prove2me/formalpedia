-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetIntegralCuspSeries_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:38:01.613898+00:00
-- url     : https://prove2.me/submissions/b34e9e9a-61ac-4416-a0d3-a80aac1f6728

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_function
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_invParameter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspNumerator_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_map


set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom
      (lpsOriginalCosetIntegralCuspSeries N hN x) =
      lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCosetBranch N hN x) := by
  rw [lpsOriginalCosetIntegralCuspSeries,lpsOriginalPhaseCuspSeries_map]
  change lpsOriginalPhaseCuspSeries ℂ N
    (lpsOriginalCosetCuspWitness N hN x).1.val
    (lpsOriginalCosetCuspWitness N hN x).1.property.ne'
    (Function.Periodic.qParam 1 ((lpsOriginalCosetCuspWitness N hN x).2.val : ℂ)) = _
  rw [lpsOriginalPhaseCuspSeries,lpsOriginalPhaseCuspNumerator_taylor N hN]
  · rw [lpsOriginalAnalyticCosetBranch,lpsOriginalAnalyticCuspAffineBranch,
      map_mul,map_pow,lpsOriginalAnalyticCuspLocalizedTaylor_invParameter,
      lpsOriginalAnalyticCuspLocalizedTaylor_function]
    rfl
  · exact (lpsOriginalCosetCuspWitness N hN x).2.property.2.1
end QEC.Coding.TannerLiftedProduct
