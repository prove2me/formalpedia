-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.scaleFive_actual_original_root_witness_not_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:37:32.501237+00:00
-- url     : https://prove2.me/submissions/b690fca0-fcfa-4a45-b240-d6f9b109e039

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_exists_actual_original_root_witness_not_boundary

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
theorem _root_.solution :
    ∃ sigma : (indexedFamily scaleFive 4).Syndrome (4 : LevelIndex 4),
      (BDL26CanonicalHistoryMarks.baseInput scaleFive 2 sigma).val ≠ 0 ∧
      topWitness scaleFive sigma ∉
        LinearMap.range ((indexedFamily scaleFive 4).coboundary1 (4 : LevelIndex 4)) :=
  exists_actual_original_root_witness_not_boundary scaleFive
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
