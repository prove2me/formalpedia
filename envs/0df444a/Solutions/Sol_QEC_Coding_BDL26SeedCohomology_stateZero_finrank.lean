-- Prove2me | solution 1 for QEC.Coding.BDL26SeedCohomology.stateZero_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:51:44.721016+00:00
-- url     : https://prove2.me/submissions/ee20d7cb-54d4-48b2-8fe3-2c8ac5cb5414

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_finrank_eq_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26SeedCohomology
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance
namespace QEC.Coding.BDL26SeedCohomology
theorem _root_.solution (S : OddScale) :
    Module.finrank Field (BDL26LevelTwoDecoder.presentationComplex
      (BDL26DecodingGraph.state S 0).presentation).middleCohomology = 1 :=
  finrank_eq_one
end QEC.Coding.BDL26SeedCohomology
