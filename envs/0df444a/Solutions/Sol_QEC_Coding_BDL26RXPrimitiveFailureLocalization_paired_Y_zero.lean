-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.paired_Y_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:40:47.648186+00:00
-- url     : https://prove2.me/submissions/811ac8ea-3549-4c70-a74a-b70884514b1e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_paired_Y_zero
import Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_paired_Y_zero
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_paired_Y_zero
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_paired_Y_zero


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
open QEC.Semantics BDL26PairedDecoderPhase
namespace QEC.Coding.BDL26RXPrimitiveFailureLocalization
theorem _root_.solution (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    BDL26LogicalDefectProtection.dX S N s (CSSDaviesLocality.singlePauli q .y)=0 :=
  BDL26LocalSearchFailureReduction.paired_Y_zero S N s q hs (safe_search S N s.1 q hs hSafe)
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
