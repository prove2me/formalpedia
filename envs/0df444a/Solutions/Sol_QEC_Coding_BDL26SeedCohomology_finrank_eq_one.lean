-- Prove2me | solution 1 for QEC.Coding.BDL26SeedCohomology.finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:39:47.600999+00:00
-- url     : https://prove2.me/submissions/e0807daa-f6e6-41ee-b5ad-e7858c8674d9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26SeedCohomology
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance
namespace QEC.Coding.BDL26SeedCohomology
theorem _root_.solution : Module.finrank Field H1 = 1 := by
  rw [equivalence.finrank_eq]
  exact Module.finrank_self Field
end QEC.Coding.BDL26SeedCohomology
