-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.backward_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:01:20.490196+00:00
-- url     : https://prove2.me/submissions/125aea20-cec2-4dca-b606-25140603304d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance
namespace QEC.Coding.BDL26RZCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (w : Cocycle (successor P A4 S)) :
    backward P A4 S (classOf (successor P A4 S) w) =
      classOf P (backwardCocycle P A4 S w) := rfl
end QEC.Coding.BDL26RZCohomology
