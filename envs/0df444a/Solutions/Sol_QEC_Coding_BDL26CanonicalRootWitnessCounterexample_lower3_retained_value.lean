-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_retained_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:52:28.582439+00:00
-- url     : https://prove2.me/submissions/c46ceb1c-71a2-4b1f-92f1-ad3f1c58fb57

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_val
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_G_boundary_at_retained
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_diagonal
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_selectedMap_eq_rx_of_odd_input
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

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
private theorem selected_RX_diagonal (S : OddScale)
    (word : (CF S).Cochain2 (2 : StepIndex 4).castSucc)
    (z : (state S 2).presentation.Z) (b : Fin 2) :
    ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 word
      ((A S).induced.zPairEquiv (z,b)).val = word z := by
  have hm : ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 word =
      ((indexedDecoderData S 4).rxMap (2 : StepIndex 4)).map2 word :=
    congrArg (fun m : BDL26CochainMap (CF S) (2 : StepIndex 4) => m.map2 word)
      (selected_RX_eq S)
  exact (congrArg (fun w : Word3 S => w ((A S).induced.zPairEquiv (z,b)).val) hm).trans
    ((A S).induced.map2_diagonal word z b)
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
open BDL26RXLocalReplacement BDL26RXStagedRestriction
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) (b : Fin 2) :
    (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val =
      1 + localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b) := by
  calc
    (lower3 S).val ((A S).induced.zPairEquiv (r2 S,b)).val =
        ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 (gamma2 S).val
            ((A S).induced.zPairEquiv (r2 S,b)).val +
          d3 S (G S) ((A S).induced.zPairEquiv (r2 S,b)).val :=
      congrArg (fun w : Word3 S => w ((A S).induced.zPairEquiv (r2 S,b)).val) (lower3_val S)
    _ = (gamma2 S).val (r2 S) +
        localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b) :=
      congrArg₂ (fun a c : BDL26Field => a+c)
        (selected_RX_diagonal S (gamma2 S).val (r2 S) b) (G_boundary_at_retained S b)
    _ = _ := congrArg (fun a : BDL26Field =>
      a + localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b))
        (gamma2_at_r2 S)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
