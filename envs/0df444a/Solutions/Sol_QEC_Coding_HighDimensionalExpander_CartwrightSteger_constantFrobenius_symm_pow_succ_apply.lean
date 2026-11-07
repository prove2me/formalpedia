-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:19:47.403204+00:00
-- url     : https://prove2.me/submissions/8cbe51c5-526e-4da4-ae0f-460fa8a3ac89

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (n : ℕ) (c : ConstantExtension P r) :
    (constantFrobenius P r).symm
        ((constantFrobenius P r ^ (n + 1)) c) =
      (constantFrobenius P r ^ n) c := by
  have hcancel :
      (constantFrobenius P r)⁻¹ *
          constantFrobenius P r ^ (n + 1) =
        constantFrobenius P r ^ n := by
    rw [pow_succ]
    group
  change
    ((constantFrobenius P r)⁻¹ *
        constantFrobenius P r ^ (n + 1)) c = _
  rw [hcancel]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
