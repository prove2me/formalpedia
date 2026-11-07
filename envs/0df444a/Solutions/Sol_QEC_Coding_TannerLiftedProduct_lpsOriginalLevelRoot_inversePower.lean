-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_inversePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:16:06.207201+00:00
-- url     : https://prove2.me/submissions/3bb92b07-f708-4461-88af-4695b14a9857

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type*) [CommRing R] (N : ℕ) (hN : 0 < N)
    (ζ : R) (hζ : ζ^N = 1) : ζ * ζ^(N-1) = 1 := by
  rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hN]
  exact hζ
end QEC.Coding.TannerLiftedProduct
