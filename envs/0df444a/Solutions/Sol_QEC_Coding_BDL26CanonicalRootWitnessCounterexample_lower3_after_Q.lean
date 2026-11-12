-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_after_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:50:16.462403+00:00
-- url     : https://prove2.me/submissions/25a1ca6e-b041-44e8-968f-5cb867ab0144

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_val
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_after_X
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_actual_Q_total

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
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) :
    rxSigmaAfterCq (A S) (lower3 S).val =
      ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 (gamma2 S).val := by
  rw [rxSigmaAfterCq,lower3_after_X,lower3_actual_Q_total,lower3_val,
    add_assoc,ZModModule.add_self,add_zero]
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
