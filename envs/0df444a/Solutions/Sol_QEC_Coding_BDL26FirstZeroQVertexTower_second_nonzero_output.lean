-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroQVertexTower.second_nonzero_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:42:05.049183+00:00
-- url     : https://prove2.me/submissions/49d0e6f1-4f1c-41de-a443-bc5adb91c4b3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_second_search
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_search
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_second_search
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_successful_nonzero_output


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroQVertexTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroQVertexTower
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0)
    (ht : secondReadout S n u q≠0) : D S (secondReadout S n u q)≠0 :=
  BDL26LevelTwoLocalBranchEndpoint.successful_nonzero_output S _
    (second_search S n u q t hs) ht
end QEC.Coding.BDL26FirstZeroQVertexTower
