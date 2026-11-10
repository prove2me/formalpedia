-- Prove2me | solution 1 for QEC.Coding.BDL26SeedCohomology.equivalence_classOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:33:24.051768+00:00
-- url     : https://prove2.me/submissions/839f734e-95ed-4047-a3b7-a2e7863c6dac

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26SeedCohomology
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance
namespace QEC.Coding.BDL26SeedCohomology
theorem _root_.solution (w : Cocycle) :
    equivalence (classOf w) = coefficient w.1 := rfl
end QEC.Coding.BDL26SeedCohomology
