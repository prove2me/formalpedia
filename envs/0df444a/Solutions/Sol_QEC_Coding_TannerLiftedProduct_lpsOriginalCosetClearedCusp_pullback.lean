-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetClearedCusp_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:21:44.593083+00:00
-- url     : https://prove2.me/submissions/d00408e3-4074-412d-873f-a53f0b35cae0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_pullback


set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) (σ : ℍ) :
    lpsOriginalClearedAffineCusp (N^2)
      (lpsOriginalCosetCuspWitness N hN x).1.val
      (lpsOriginalCosetCuspWitness N hN x).2.val
      (Function.Periodic.qParam 1 (σ : ℂ)) =
      Function.Periodic.qParam 1 (σ : ℂ)^(N^2) *
        lpsOriginalJDilated N hN
          (x.out.val⁻¹ • (lpsE2AffineMatrix N hN 0 • σ)) := by
  let w := lpsOriginalCosetCuspWitness N hN x
  rw [lpsOriginalClearedAffineCusp_pullback (N^2) w.1.val w.1.property
    w.2.property.1 w.2.val σ, ← w.2.property.2.2 σ]
end QEC.Coding.TannerLiftedProduct
