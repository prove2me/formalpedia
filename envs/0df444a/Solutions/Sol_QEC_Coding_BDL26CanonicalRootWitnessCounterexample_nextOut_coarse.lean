-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.nextOut_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:59:58.212461+00:00
-- url     : https://prove2.me/submissions/129bfa6e-1df9-4139-a683-c39c0cf97be3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_actual_coarse
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_topOut_coarse

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
theorem _root_.solution (S : OddScale) : (nextOut S).coarse = gamma2 S := by
  change (actualStep S 4 (2 : StepIndex 4) (topOut S).coarse).coarse = _
  rw [topOut_coarse,actualStep_rx S 4 2 (by decide)]
  exact lower3_actual_coarse S
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
