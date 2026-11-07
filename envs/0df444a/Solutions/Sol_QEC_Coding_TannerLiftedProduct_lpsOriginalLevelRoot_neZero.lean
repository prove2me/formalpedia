-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_neZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:13:27.999768+00:00
-- url     : https://prove2.me/submissions/585ede89-1441-42a0-bd1a-d668762c679b

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
    (R : Type*) [CommRing R] [Nontrivial R] (N : ℕ) (hN : 0 < N)
    (ζ : R) (hζ : ζ^N = 1) : ζ ≠ 0 := by
  intro h
  rw [h, zero_pow hN.ne'] at hζ
  exact zero_ne_one hζ
end QEC.Coding.TannerLiftedProduct
