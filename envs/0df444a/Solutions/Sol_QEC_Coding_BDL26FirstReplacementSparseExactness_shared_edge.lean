-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.shared_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:16:13.870198+00:00
-- url     : https://prove2.me/submissions/d6a7d7b4-0858-4202-9272-97d301f75054

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness
theorem _root_.solution (b : Fin 2) :
    xStarFaceXQEdge Seed center (oldFace b) 1 =
      xStarFaceXQEdge Seed center (oldFace 0) 1 := by
  fin_cases b <;> rfl
end QEC.Coding.BDL26FirstReplacementSparseExactness
