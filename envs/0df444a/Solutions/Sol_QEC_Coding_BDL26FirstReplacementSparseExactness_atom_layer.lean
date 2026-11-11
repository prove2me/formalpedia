-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.atom_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:27:38.098952+00:00
-- url     : https://prove2.me/submissions/9118c23f-aadf-4c48-a97b-8a0d81c3322c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_horizontal_tag

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness
theorem _root_.solution (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (a : Atom S) :
    interiorLayer S (atom S large k a) = k.val := by
  rcases a with b | ⟨b,i⟩
  · rfl
  · rw [atom,horizontal_tag]
    rfl
end QEC.Coding.BDL26FirstReplacementSparseExactness
