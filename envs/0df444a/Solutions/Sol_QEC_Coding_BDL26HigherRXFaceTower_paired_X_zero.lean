-- Prove2me | solution 1 for QEC.Coding.BDL26HigherRXFaceTower.paired_X_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:55:59.421365+00:00
-- url     : https://prove2.me/submissions/2f694f68-2069-4973-aa2b-23ee02c0e1ad

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_paired_X_zero


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
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .x)=0 :=
  BDL26BoundaryTailInvariance.paired_X_zero S n s q (stopIndex t) 0
    (stop_boundary S n s.1 q t)
end QEC.Coding.BDL26HigherRXFaceTower
