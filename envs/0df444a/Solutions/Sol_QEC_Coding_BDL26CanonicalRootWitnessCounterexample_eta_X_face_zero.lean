-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.eta_X_face_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:57:25.995914+00:00
-- url     : https://prove2.me/submissions/52ea26cd-9a4f-4c85-bf49-f749df6ebab4

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
theorem _root_.solution (S : OddScale) (x : (state S 2).presentation.X)
    (f : DoubleCylinderFace (state S 2).presentation x S) :
    eta S (xFace3 S x f) = 0 := by
  have hn := actual_unparented_top_not_root S (upper4 S) (xFace3 S x f) (by rfl)
  exact selectedWord_zero _ _ (xFace3 S x f) hn
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
