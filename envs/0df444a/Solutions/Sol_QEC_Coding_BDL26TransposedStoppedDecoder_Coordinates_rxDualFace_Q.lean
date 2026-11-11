-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:49:49.591201+00:00
-- url     : https://prove2.me/submissions/8cf63511-5df7-48b5-b3b2-f19fb54a9f1d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qToZ_edge_raw

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
    (f : RXFace P S) (b : Two) :
    rzFaceQ (transposePresentation P) A S (rxDualFace P S f) b =
      rxDualQ P S (rxFaceQ P S f b) := by
  rcases f with ⟨x,f,c⟩ | (⟨a,e,c⟩ | ⟨f,c⟩)
  · rcases f with copy | boundary
    · rcases c with ⟨horizontal,vertical⟩
      fin_cases horizontal <;> fin_cases vertical <;> fin_cases b <;> rfl
    · rcases c with ⟨copy,corner⟩
      fin_cases corner <;> fin_cases b <;> rfl
  · fin_cases b
    · exact congrArg (fun w : DoubleCylinderEdge P a.1.1 S =>
        (Sum.inl (⟨a.1.1,w⟩ : Sigma fun x : P.X => DoubleCylinderEdge P x S) : RX1 P S))
        (qToZ_edge_raw (transposePresentation P) A a.1.2 a.1.1 a.2 S e)
    · rfl
  · rfl
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
