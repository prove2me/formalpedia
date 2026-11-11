-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.face_arm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:16:26.859975+00:00
-- url     : https://prove2.me/submissions/dc1c4050-ffb7-46f8-8655-17c78908f698

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
    (xStarFaceQZEdge Seed center (oldFace b) 0).val =
      Sum.inr ⟨(oldQ b,b), (armEdge b).property⟩ := by
  fin_cases b <;> rfl
end QEC.Coding.BDL26FirstReplacementSparseExactness
