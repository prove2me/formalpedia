-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceEdgeTower.seed_parent_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:04:56.897857+00:00
-- url     : https://prove2.me/submissions/fb36fc2f-31ff-43c8-9072-e6f64aca1980

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxPhysical_localEdge_parent_none


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceEdgeTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXFaceEdgeTower
theorem _root_.solution (S : OddScale) (a : Seed S) :
    parent S 3 (Vertex.q (seedPhysical S a))=none :=
  BDL26RXDecoderAdapter.rxPhysical_localEdge_parent_none S 3 ⟨2,by omega⟩
    (by decide) (faceOwner S a.1 a.2.1) a.2.2
end QEC.Coding.BDL26RXFaceEdgeTower
