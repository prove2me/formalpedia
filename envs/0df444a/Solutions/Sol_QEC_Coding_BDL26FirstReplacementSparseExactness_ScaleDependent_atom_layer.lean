-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.atom_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:56:07.386707+00:00
-- url     : https://prove2.me/submissions/9e8a570a-4e38-4754-acbb-ae15fe66045a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_horizontal_tag
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_horizontal_tag

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
theorem _root_.solution (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (a : Atom S) :
    interiorLayer S (atom S n large k a) = k.val := by
  rcases a with b | ⟨b,i⟩
  · rfl
  · rw [atom,horizontal_tag]
    rfl
end QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
