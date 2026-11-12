-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_top_output_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:44:30.168896+00:00
-- url     : https://prove2.me/submissions/db613273-3649-464f-bc4c-8bdf965ccd95

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_outputAt_top
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2) :
    (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (1 : StepIndex 2)).input = sigma := by
  have hot := BDL26CanonicalHistoryMarks.outputAt_top S 1 sigma
  change BDL26CanonicalHistoryMarks.outputAt S 2 sigma (1 : StepIndex 2) =
    actualStep S 4 (3 : StepIndex 4) sigma at hot
  exact (congrArg AssemblyStepOutput.input hot).trans
    ((actualStep_relation S 4 (3 : StepIndex 4)).input_eq sigma)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
