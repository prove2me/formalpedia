-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.topOut_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:09:44.854207+00:00
-- url     : https://prove2.me/submissions/6df2c442-1290-4096-8f37-6f8af7dfd853

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_map2_coarse


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
theorem _root_.solution (S : OddScale) : (topOut S).coarse = lower3 S := by
  change (actualStep S 4 (3 : StepIndex 4) (upper4 S)).coarse = _
  rw [actualStep_rz S 4 3 (by decide)]
  exact rzStepOutput_map2_coarse S 4 3 (by decide) (lower3 S)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
