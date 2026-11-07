-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelRoot_inversePower_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:41:55.091168+00:00
-- url     : https://prove2.me/submissions/fc6310a8-9fa9-4569-be32-1664e4839132

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_neZero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_inversePower

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (R : Type*) [Field R]
    (N : ℕ) (hN : 0 < N) (ζ : R) (hζ : ζ^N = 1) :
    ζ^(N-1) = ζ⁻¹ := by
  apply (mul_eq_one_iff_eq_inv₀
    (lpsOriginalLevelRoot_neZero R N hN ζ hζ)).mp
  rw [mul_comm]
  exact lpsOriginalLevelRoot_inversePower R N hN ζ hζ
end QEC.Coding.TannerLiftedProduct
