-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.qPortWord_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:08:15.111998+00:00
-- url     : https://prove2.me/submissions/027dc404-3990-419c-873d-b54b770a55e6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXFaceSecondReadout
theorem _root_.solution (P : TannerSquarePresentation) (q : P.Q) (b : F)
    (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) :
    qPortWord P q b (c,Sum.inl (Sum.inr z))=b := rfl
end QEC.Coding.BDL26RXFaceSecondReadout
