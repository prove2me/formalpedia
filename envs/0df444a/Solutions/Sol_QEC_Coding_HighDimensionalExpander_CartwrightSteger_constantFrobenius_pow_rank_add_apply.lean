-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_rank_add_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:19:46.361316+00:00
-- url     : https://prove2.me/submissions/c67ada2d-338c-4759-91c5-6aa5d5092ef3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_matrixRank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (n : ℕ) (c : ConstantExtension P r) :
    (constantFrobenius P r ^ (r.matrixRank + n)) c =
      (constantFrobenius P r ^ n) c := by
  rw [pow_add, constantFrobenius_pow_matrixRank]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
