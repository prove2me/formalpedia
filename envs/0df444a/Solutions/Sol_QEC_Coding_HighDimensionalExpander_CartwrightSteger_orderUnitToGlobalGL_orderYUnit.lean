-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_orderYUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:47:49.532077+00:00
-- url     : https://prove2.me/submissions/ded35616-0fb5-4425-8e54-1a7beb5debec

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    orderUnitToGlobalGL P r (cartwrightStegerOrderYUnit P r) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (Units.mk0 (splittingY P r) (splittingY_ne_zero P r)) := by
  apply Units.ext
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
