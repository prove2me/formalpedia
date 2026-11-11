-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:50:48.036281+00:00
-- url     : https://prove2.me/submissions/c35d2530-2d64-4634-87ed-29f12eb007d5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qToZ_vertex_raw
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : RZFace P S) :
    rxFaceX (transposePresentation P) S (rzDualFace P S f) =
      rzDualX P S (rzFaceZ P A S f) := by
  rcases f with ⟨z,f,b⟩ | (⟨a,e,b⟩ | ⟨f,b⟩)
  · rcases f with copy | boundary
    · rfl
    · rcases b with ⟨copy,corner⟩
      fin_cases corner <;> rfl
  · let root := qDoubleCylinderUnderlyingStarEdge (transposePresentation P) a.1.1 S e
    let v := BDL26RZLocalReplacement.edgeEndpoint
      (qDoubleCylinderEdgeStart (transposePresentation P) a.1.1 S)
      (qDoubleCylinderEdgeEnd (transposePresentation P) a.1.1 S) e b
    have hedge : BDL26RXLocalReplacement.edgeEndpoint
        (tannerDoubleCylinderEdgeStart (transposePresentation P) a.1.2 S)
        (tannerDoubleCylinderEdgeEnd (transposePresentation P) a.1.2 S)
        (qToXDoubleCylinderEdgeRaw (transposePresentation P) a.1.1 a.1.2 a.2 S e) b =
        qToXDoubleCylinderVertexAtRoot (transposePresentation P) a.1.1 a.1.2 a.2 S root v := by
      fin_cases b
      · exact (qToXDoubleCylinderEdgeRaw_start (transposePresentation P) a.1.1 a.1.2 a.2 S root e).symm
      · exact (qToXDoubleCylinderEdgeRaw_end (transposePresentation P) a.1.1 a.1.2 a.2 S root e).symm
    exact congrArg (fun w : DoubleCylinderVertex (transposePresentation P) a.1.2 S =>
      (⟨a.1.2,w⟩ : RX0 (transposePresentation P) S))
      (hedge.trans (qToZ_vertex_raw P A a.1.1 a.1.2 a.2 S root v).symm)
  · rfl
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
