-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.eta_X_query_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:02:10.994542+00:00
-- url     : https://prove2.me/submissions/833421de-1b64-4240-a720-141bc61d96e7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_center_qEdge3
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_word3_coordinate_cases
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_X_face_zero
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
private theorem restriction_zero_of_values {I : Type} [Fintype I] [DecidableEq I]
    (R : Finset I) (word : I → BDL26Field) (hz : ∀ p, p ∈ R → word p = 0) :
    restrictWordLinear R word = 0 := by
  funext p
  exact hz p.val p.property
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
private theorem word3_X_query_zero_of_aux_zero (S : OddScale) (word : Word3 S)
    (hface : ∀ x f, word (xFace3 S x f) = 0)
    (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x) word = 0 := by
  apply restriction_zero_of_values
  intro p hp
  have ho := ((A S).topCenter_x_iff x p).mp hp
  rcases word3_coordinate_cases S p with ⟨y,f,he⟩ | ⟨q,e,he⟩ | ⟨z,b,he⟩
  · exact (congrArg word he).trans (hface y f)
  · have hc := congrArg (A S).topCenter he
    have hbad : Sum.inr (Sum.inl q) = Sum.inl x :=
      (center_qEdge3 S q e).symm.trans (hc.symm.trans ho)
    cases hbad
  · have hc := congrArg (A S).topCenter he
    have hbad : Sum.inr (Sum.inr z) = Sum.inl x :=
      ((A S).topCenter_coarse_pair z b).symm.trans (hc.symm.trans ho)
    cases hbad
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
theorem _root_.solution (S : OddScale) (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x) (eta S) = 0 :=
  word3_X_query_zero_of_aux_zero S (eta S) (eta_X_face_zero S) x
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
