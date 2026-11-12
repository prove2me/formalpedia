-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.exists_actual_original_root_witness_not_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:45:40.968798+00:00
-- url     : https://prove2.me/submissions/d2ead482-935c-423b-9405-92deddaf7ab0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_gamma2_nonzero
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_base_input
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_top_witness_not_boundary

set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) :
    ∃ sigma : (indexedFamily S 4).Syndrome (4 : LevelIndex 4),
      (BDL26CanonicalHistoryMarks.baseInput S 2 sigma).val ≠ 0 ∧
      topWitness S sigma ∉
        LinearMap.range ((indexedFamily S 4).coboundary1 (4 : LevelIndex 4)) := by
  refine ⟨upper4 S,?_,actual_top_witness_not_boundary S⟩
  rw [actual_base_input]
  exact gamma2_nonzero S
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
