-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroFaceEndpoint.face_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:47:20.542607+00:00
-- url     : https://prove2.me/submissions/48ce14a1-417f-456b-b4b2-8f9030b0d276

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_face_parity_zero


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroFaceEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroFaceEndpoint
theorem _root_.solution (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) : parity S h=0 :=
  BDL26LevelTwoLocalBranchEndpoint.face_parity_zero S z f h hh
end QEC.Coding.BDL26FirstZeroFaceEndpoint
