-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceEdgeTower.face_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:59:20.740174+00:00
-- url     : https://prove2.me/submissions/3e39d68a-8970-4d2e-881c-cb199e9049d3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_local_face_data


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
theorem _root_.solution (S : OddScale) (z : (RawOne S).Z)
    (f : ZDoubleCylinderFace (RawOne S) z S) :
    BDL26RZPhysicalXStarTransport.Q0 S 2 ⟨1,by omega⟩ (by decide) (faceOwner S z f)=∅ ∧
    BDL26RZPhysicalXStarTransport.Z0 S 2 ⟨1,by omega⟩ (by decide) (faceOwner S z f)={z} := by
  have h := BDL26RZPhysicalXStarTransport.local_face_data S 2 ⟨1,by omega⟩ (by decide) z f
  exact ⟨h.1,h.2.1⟩
end QEC.Coding.BDL26RXFaceEdgeTower
