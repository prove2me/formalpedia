-- Prove2me | solution 1 for QEC.Coding.BDL26HigherRXFaceTower.actual_Y_package
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:48:21.332402+00:00
-- url     : https://prove2.me/submissions/8714bde9-4e98-47a2-ab25-4be2431b7758

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_actual_Y_package


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
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
      (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
        BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 :=
  BDL26BoundaryTailInvariance.actual_Y_package S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)
end QEC.Coding.BDL26HigherRXFaceTower
