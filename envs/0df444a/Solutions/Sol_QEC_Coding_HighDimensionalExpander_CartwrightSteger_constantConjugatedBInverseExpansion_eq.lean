-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantConjugatedBInverseExpansion_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:20:03.752227+00:00
-- url     : https://prove2.me/submissions/79bc5917-f67c-4050-91f0-a0ab767cb20b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    constantConjugatedBInverseExpansion P r u =
      1 + (splittingY P r)⁻¹ •
        constantConjugatedBInverseTail P r u := by
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
