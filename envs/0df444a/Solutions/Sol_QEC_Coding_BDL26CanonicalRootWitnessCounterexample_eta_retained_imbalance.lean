-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.eta_retained_imbalance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:25:05.760249+00:00
-- url     : https://prove2.me/submissions/024c5e9d-1b03-47a2-9af3-fffbb83c2395

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_retained_imbalance
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_retained_value
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
theorem _root_.solution (S : OddScale) :
    eta S ((A S).induced.zPairEquiv (r2 S,0)).val +
      eta S ((A S).induced.zPairEquiv (r2 S,1)).val = 1 := by
  exact (congrArg₂ (fun a b : BDL26Field => a+b)
    (eta_retained_value S 0) (eta_retained_value S 1)).trans (lower3_retained_imbalance S)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
