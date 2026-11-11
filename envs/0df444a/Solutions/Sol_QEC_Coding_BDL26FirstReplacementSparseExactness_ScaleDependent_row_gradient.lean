-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.row_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:44:44.4653+00:00
-- url     : https://prove2.me/submissions/1af7bb03-7d41-4478-ac90-a34b08aaa566

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_sum_adjacent
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_horizontal_gradient
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_horizontal_gradient
import Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_sum_adjacent


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
theorem _root_.solution (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1))
    (b : Fin 2) (p : V S) :
    (∑ i : Fin S.half, rxCoboundary0 Seed S p (horizontal S n large k b i))=
      p (grid S n large k b 0)+p (grid S n large k b (Fin.last S.half)) := by
  simp_rw [horizontal_gradient]
  exact sum_adjacent S.half (fun i => p (grid S n large k b i))
end QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
