-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.top_RZ_reflects_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:38:11.295426+00:00
-- url     : https://prove2.me/submissions/fabd73ba-7d3f-4433-9839-55ea664c0ebe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
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
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) (eta : Word3 S)
    (h : ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 eta ∈
      LinearMap.range ((CF S).coboundary1 level4)) :
    eta ∈ LinearMap.range (d3 S) := by
  obtain ⟨e,he⟩ := h
  let Z := rzData S 4 (3 : StepIndex 4) (by decide)
  refine ⟨Z.induced.correctionProjection e,?_⟩
  have hc := rzData_inducedCoboundaryCompatibility S 4 (3 : StepIndex 4) (by decide) e
  change RZCoarseGraining.RZCoarseGrainingData.topParity Z
    (((CF S).coboundary1 level4) e) =
      d3 S (Z.induced.correctionProjection e) at hc
  rw [he] at hc
  have hm : RZCoarseGraining.RZCoarseGrainingData.topParity Z
      (((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 eta) = eta := by
    rw [selectedMap_eq]
    exact RZCoarseGraining.topParity_rzMap_map2 Z eta
  exact hc.symm.trans hm
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
