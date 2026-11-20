-- Prove2me | solution 1 for QEC.Coding.BDL26RXPrimitiveFailureLocalization.actual_Y_package
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:16:29.606074+00:00
-- url     : https://prove2.me/submissions/82c1fc22-f953-47a3-b2d9-543eab28e051

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_actual_Y_package


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
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S (N+2) q .y*BDL26PairedDecoderChannel.dressedZ S N-
      BDL26PairedDecoderChannel.dressedZ S N*BDL26CSSDaviesLocality.coupling S (N+2) q .y)*
      atom S N s=0 :=
  BDL26LocalSearchFailureReduction.actual_Y_package S N s q hs (safe_search S N s.1 q hs hSafe)
end QEC.Coding.BDL26RXPrimitiveFailureLocalization
