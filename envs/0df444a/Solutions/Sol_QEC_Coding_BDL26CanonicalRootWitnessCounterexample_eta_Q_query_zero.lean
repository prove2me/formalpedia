-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.eta_Q_query_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:01:37.517776+00:00
-- url     : https://prove2.me/submissions/f99a1ed0-d02b-4588-850d-588014f02748

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_center_xFace3
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_word3_coordinate_cases
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_Q_edge_zero
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
private theorem word3_Q_query_zero_of_aux_zero (S : OddScale) (word : Word3 S)
    (hedge : ∀ q e, word (qEdge3 S q e) = 0)
    (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q) word = 0 := by
  apply restriction_zero_of_values
  intro p hp
  have ho := ((A S).topCenter_q_iff q p).mp hp
  rcases word3_coordinate_cases S p with ⟨x,f,he⟩ | ⟨r,e,he⟩ | ⟨z,b,he⟩
  · have hc := congrArg (A S).topCenter he
    have hbad : Sum.inl x = Sum.inr (Sum.inl q) :=
      (center_xFace3 S x f).symm.trans (hc.symm.trans ho)
    cases hbad
  · exact (congrArg word he).trans (hedge r e)
  · have hc := congrArg (A S).topCenter he
    have hbad : Sum.inr (Sum.inr z) = Sum.inr (Sum.inl q) :=
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
theorem _root_.solution (S : OddScale) (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q) (eta S) = 0 :=
  word3_Q_query_zero_of_aux_zero S (eta S) (eta_Q_edge_zero S) q
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
