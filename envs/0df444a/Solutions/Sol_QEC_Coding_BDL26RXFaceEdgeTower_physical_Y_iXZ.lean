-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceEdgeTower.physical_Y_iXZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:46:49.601991+00:00
-- url     : https://prove2.me/submissions/2bf47701-e585-4f4c-ad99-163cbbe8e3cd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_physical_Y_iXZ
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_Y_iXZ
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_physical_Y_iXZ
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_physical_Y_iXZ


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
open QEC.Semantics BDL26PairedDecoderPhase
namespace QEC.Coding.BDL26RXFaceEdgeTower
theorem _root_.solution (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) :=
  BDL26ActualFailureReadout.physical_Y_iXZ S n q
end QEC.Coding.BDL26RXFaceEdgeTower
