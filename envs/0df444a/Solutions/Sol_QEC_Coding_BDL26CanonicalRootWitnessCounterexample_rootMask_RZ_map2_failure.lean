-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_RZ_map2_failure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:25:09.793354+00:00
-- url     : https://prove2.me/submissions/72549fa5-570f-43b8-99ba-cfe591202c75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_topWitness_factor
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_Q_query_zero
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_nonzero_Q_coordinate
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_mid_Q_value
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_topParity_rzMap_map2
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) :
    topWitness S (upper4 S) ≠
      ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 (rootMaskMidWord S) := by
  let Z := rzData S 4 (3 : StepIndex 4) (by decide)
  have hleft (word : Word3 S) : RZCoarseGraining.RZCoarseGrainingData.topParity Z
      (((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 word) = word := by
    rw [selectedMap_eq]
    exact RZCoarseGraining.topParity_rzMap_map2 Z word
  have hinj (a b : Word3 S)
      (hab : ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 a =
        ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 b) : a = b :=
    (hleft a).symm.trans
      ((congrArg (RZCoarseGraining.RZCoarseGrainingData.topParity Z) hab).trans (hleft b))
  have hrestrict_eval {I : Type} [Fintype I]
      (Y : Finset I) (word : Word BDL26Field I) (p : LocalRegionIndex Y) :
      (restrictWordLinear Y word) p = word p.val := rfl
  have hneq : eta S ≠ rootMaskMidWord S := by
    intro hsame
    obtain ⟨p,hp⟩ := rootMask_nonzero_Q_coordinate S
    have hval : eta S p.val = rootMaskMidWord S p.val :=
      congrArg (fun word : Word3 S => word p.val) hsame
    have hz0 := congrArg
      (fun word : LocalRegionIndex ((LQ S).syndromeRegion (q2 S)) → BDL26Field => word p)
      (eta_Q_query_zero S (q2 S))
    have hz := (hrestrict_eval ((LQ S).syndromeRegion (q2 S)) (eta S) p).symm.trans hz0
    exact hp ((rootMask_mid_Q_value S p).symm.trans (hval.symm.trans hz))
  intro he
  exact hneq (hinj (eta S) (rootMaskMidWord S) ((topWitness_factor S).symm.trans he))
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
