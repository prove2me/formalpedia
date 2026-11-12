-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.eta_Q_edge_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:57:29.28654+00:00
-- url     : https://prove2.me/submissions/500c22a3-6951-407d-8e1a-78b4d1de1b1b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_unparented_top_not_root
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
private theorem selectedWord_apply {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) :
    selectedWord P word p = if P p then word p else 0 := rfl
private theorem selectedWord_zero {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) (hp : ¬ P p) : selectedWord P word p = 0 :=
  (selectedWord_apply P word p).trans (if_neg hp)
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
theorem _root_.solution (S : OddScale) (q : (state S 2).presentation.Q)
    (e : QDoubleCylinderEdge (state S 2).presentation q S) :
    eta S (qEdge3 S q e) = 0 := by
  have hn := actual_unparented_top_not_root S (upper4 S) (qEdge3 S q e) (by rfl)
  exact selectedWord_zero _ _ (qEdge3 S q e) hn
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
