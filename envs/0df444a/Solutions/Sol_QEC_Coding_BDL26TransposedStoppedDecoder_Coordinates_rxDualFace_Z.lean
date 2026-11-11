-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:49:46.568249+00:00
-- url     : https://prove2.me/submissions/665345ae-4763-434d-bde3-2eae84164d48

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qToZ_vertex_raw
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement hiding Two
open BDL26RZLocalReplacement hiding Two
open BDL26RZMap1CoordinateBridge hiding Two
open BDL26RXDecoderAdapter
open MultiscaleDecoder (BDL26Field)
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible (transposePresentation P)) (S : OddScale)
    (f : RXFace P S) :
    rzFaceZ (transposePresentation P) A S (rxDualFace P S f) =
      rxDualZ P S (rxFaceX P S f) := by
  rcases f with ⟨x,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)
  · rcases f with copy | boundary
    · rfl
    · rcases b with ⟨copy,corner⟩
      fin_cases corner <;> rfl
  · let root := qDoubleCylinderUnderlyingStarEdge P a.1.2 S e
    refine (congrArg (fun v : DoubleCylinderVertex P a.1.1 S =>
      (⟨a.1.1,v⟩ : RX0 P S))
      (qToZ_vertex_raw (transposePresentation P) A a.1.2 a.1.1 a.2 S root
        (BDL26RZLocalReplacement.edgeEndpoint (qDoubleCylinderEdgeStart P a.1.2 S)
          (qDoubleCylinderEdgeEnd P a.1.2 S) e b))).trans ?_
    fin_cases b
    · exact congrArg (fun v => (⟨a.1.1,v⟩ : RX0 P S))
        (qToXDoubleCylinderEdgeRaw_start P a.1.2 a.1.1 a.2 S root e)
    · exact congrArg (fun v => (⟨a.1.1,v⟩ : RX0 P S))
        (qToXDoubleCylinderEdgeRaw_end P a.1.2 a.1.1 a.2 S root e)
  · rfl
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
