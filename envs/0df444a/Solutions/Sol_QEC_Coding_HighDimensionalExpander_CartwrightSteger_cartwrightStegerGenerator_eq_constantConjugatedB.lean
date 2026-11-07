-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_eq_constantConjugatedB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:02:08.199448+00:00
-- url     : https://prove2.me/submissions/21c304ae-460e-4275-8b46-cc5575d38141

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    cartwrightStegerGenerator P r x =
      constantConjugatedCartwrightStegerB P r
        (constantClassRepresentative P r x) :=
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
