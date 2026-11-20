-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceEdgeTower.second_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:58:48.033486+00:00
-- url     : https://prove2.me/submissions/34caf0fe-b2e3-4b1a-9c79-3cc744cf06ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_terminal_syndrome
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_terminal_local
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSuccess_iff


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
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S n u q) := by
  rw [← BDL26FirstZeroFaceEndpoint.terminal_syndrome S n u q hs]
  exact (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    ⟨terminalWord S n u q,terminal_local S n u q t,rfl⟩
end QEC.Coding.BDL26RXFaceEdgeTower
