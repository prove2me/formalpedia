-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.row_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:22:34.186205+00:00
-- url     : https://prove2.me/submissions/48b35645-94b6-414a-8ff5-1ff6fefd92ea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_sum_adjacent
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_horizontal_gradient
import Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_sum_adjacent


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness
theorem _root_.solution (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15)
    (b : Fin 2) (p : V S) :
    (∑ i : Fin S.half, rxCoboundary0 Seed S p (horizontal S large k b i))=
      p (grid S large k b 0)+p (grid S large k b (Fin.last S.half)) := by
  simp_rw [horizontal_gradient]
  exact sum_adjacent S.half (fun i => p (grid S large k b i))
end QEC.Coding.BDL26FirstReplacementSparseExactness
