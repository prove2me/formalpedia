-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_actual_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:54:31.265247+00:00
-- url     : https://prove2.me/submissions/c6cd4090-ed57-4d95-8b06-d57c2746dbc2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_after_Q
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_coarse
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_coarseProjection_eq_of_map2
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_selectedMap_eq_rx_of_odd_input
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
private theorem selected_RX_eq (S : OddScale) :
    (indexedDecoderData S 4).selectedMap (2 : StepIndex 4) =
      (indexedDecoderData S 4).rxMap (2 : StepIndex 4) :=
  selectedMap_eq_rx_of_odd_input (indexedDecoderData S 4) (2 : StepIndex 4) (by decide)
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
end

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
    (rxStepOutput S 4 (2 : StepIndex 4) (by decide) (lower3 S)).coarse = gamma2 S := by
  apply Subtype.ext
  have hm : ((indexedDecoderData S 4).rxMap (2 : StepIndex 4)).map2 (gamma2 S).val =
      ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 (gamma2 S).val :=
    (congrArg (fun m : BDL26CochainMap (CF S) (2 : StepIndex 4) => m.map2 (gamma2 S).val)
      (selected_RX_eq S)).symm
  have hp : coarseProjection (A S) (rxSigmaAfterCq (A S) (lower3 S).val) =
      (gamma2 S).val :=
    coarseProjection_eq_of_map2 (A S) _ (gamma2 S).val
      (hm.trans (lower3_after_Q S).symm)
  exact (rxStepOutput_coarse S 4 (2 : StepIndex 4) (by decide) (lower3 S)).trans hp
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
