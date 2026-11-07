-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCoefficient_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:24.713038+00:00
-- url     : https://prove2.me/submissions/4545d20a-6802-49d2-93a7-96adf82b143f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (ζ : ConstantExtension P r) :
    infinityConjugationCoefficient P r u 0 ζ =
      ζ - (constantFrobenius P r ^ (-1 : ℤ)) ζ := by
  rw [infinityConjugationCoefficient]
  norm_num
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
