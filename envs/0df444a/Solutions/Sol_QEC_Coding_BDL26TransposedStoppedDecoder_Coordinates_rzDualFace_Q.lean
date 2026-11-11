-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:47:48.704517+00:00
-- url     : https://prove2.me/submissions/d26fd1ae-7461-420a-9f8a-deb44fe3fb48

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qToZ_edge_raw
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
    (S : OddScale) (f : RZFace P S) (b : Two) :
    rxFaceQ (transposePresentation P) S (rzDualFace P S f) b =
      rzDualQ P S (rzFaceQ P A S f b) := by
  rcases f with ⟨z,f,c⟩ | (⟨a,e,c⟩ | ⟨f,c⟩)
  · rcases f with copy | boundary
    · rcases c with ⟨horizontal,vertical⟩
      fin_cases horizontal <;> fin_cases vertical <;> fin_cases b <;> rfl
    · rcases c with ⟨copy,corner⟩
      fin_cases corner <;> fin_cases b <;> rfl
  · fin_cases b
    · exact (congrArg (fun w : DoubleCylinderEdge (transposePresentation P) a.1.2 S =>
        (Sum.inl (⟨a.1.2,w⟩ : Sigma fun z : P.Z =>
          DoubleCylinderEdge (transposePresentation P) z S) : RX1 (transposePresentation P) S))
        (qToZ_edge_raw P A a.1.1 a.1.2 a.2 S e)).symm
    · rfl
  · rfl
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
