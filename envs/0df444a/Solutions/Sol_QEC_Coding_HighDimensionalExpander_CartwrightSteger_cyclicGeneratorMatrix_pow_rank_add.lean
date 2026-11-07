-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorMatrix_pow_rank_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:01:38.467301+00:00
-- url     : https://prove2.me/submissions/d08e77d8-1ec0-43a9-a6d4-73f60a2f65e6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_matrixRank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (n : ℕ) :
    cyclicGeneratorMatrix P r ^ (r.matrixRank + n) =
      (onePlusY P r) • cyclicGeneratorMatrix P r ^ n := by
  rw [pow_add, cyclicGenerator_pow_matrixRank]
  rw [smul_mul_assoc, one_mul]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
