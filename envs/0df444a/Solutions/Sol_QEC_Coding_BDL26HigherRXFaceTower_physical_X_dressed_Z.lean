-- Prove2me | solution 1 for QEC.Coding.BDL26HigherRXFaceTower.physical_X_dressed_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:27.070996+00:00
-- url     : https://prove2.me/submissions/97f6d615-61ae-46cf-8b4b-f8d62f679065

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_physical_X_dressed_Z


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HigherRXFaceTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators
open QEC.Semantics BDL26PairedDecoderPhase
namespace QEC.Coding.BDL26HigherRXFaceTower
theorem _root_.solution (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Family S n q) :
    (PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*PauliSymplectic.toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S n s=0 :=
  BDL26BoundaryTailInvariance.physical_X_dressed_Z S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)
end QEC.Coding.BDL26HigherRXFaceTower
