-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.forward_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:03:52.623337+00:00
-- url     : https://prove2.me/submissions/f31703a1-5ccd-4da7-b363-e61a6e6bab1b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance
namespace QEC.Coding.BDL26RZCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (v : Cocycle P) :
    forward P A4 S (classOf P v) =
      classOf (successor P A4 S) (forwardCocycle P A4 S v) := rfl
end QEC.Coding.BDL26RZCohomology
