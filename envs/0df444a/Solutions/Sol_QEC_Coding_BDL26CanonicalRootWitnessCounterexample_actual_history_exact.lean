-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_history_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:10:42.068786+00:00
-- url     : https://prove2.me/submissions/4bf143ff-f1ff-40ef-b13c-e7cbf0984eae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_two


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
theorem _root_.solution (S : OddScale) : actualHistory S 2 (upper4 S) =
    [CorrectionHistoryEntry.step (1 : StepIndex 2)
       (LevelTwoHistory.suffixOutput (indexedDecoderData S 4) 1 (topOut S)),
     CorrectionHistoryEntry.step (0 : StepIndex 2)
       (LevelTwoHistory.suffixOutput (indexedDecoderData S 4) 0 (nextOut S)),
     CorrectionHistoryEntry.base (storedBase S)] := by
  exact LevelTwoHistory.stoppedHistory_two (indexedDecoderData S 4)
    (actualAboveTwoSteps S 2) (actualBase S 2) (upper4 S)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
