-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_integralArithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:03:15.908048+00:00
-- url     : https://prove2.me/submissions/74d7b311-892e-480f-87cb-3f501e1629fd

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToGlobalSkewScalarRange_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (a : IntegralArithmeticRing P) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f =
        functionFieldScalarMatrix P r
          (integralArithmeticToFunctionField P a) := by
  obtain ⟨f, hf⟩ := (integralArithmeticToGlobalSkewScalarRange P r a).property
  refine ⟨f, ?_⟩
  rw [← integralArithmeticToGlobalSkewScalarRange_coe P r a]
  exact hf
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
