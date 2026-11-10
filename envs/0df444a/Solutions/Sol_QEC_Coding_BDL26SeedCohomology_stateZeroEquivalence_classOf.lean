-- Prove2me | solution 1 for QEC.Coding.BDL26SeedCohomology.stateZeroEquivalence_classOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:33:40.000724+00:00
-- url     : https://prove2.me/submissions/5d366ea5-0188-4dfd-9822-64dbf2b6057e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26SeedCohomology
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance
namespace QEC.Coding.BDL26SeedCohomology
theorem _root_.solution (S : OddScale) (w : Cocycle) :
    stateZeroEquivalence S (classOf w) = coefficient w.1 := rfl
end QEC.Coding.BDL26SeedCohomology
