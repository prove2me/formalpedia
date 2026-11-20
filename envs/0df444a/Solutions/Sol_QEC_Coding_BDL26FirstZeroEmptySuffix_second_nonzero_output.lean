-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.second_nonzero_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:11:48.551619+00:00
-- url     : https://prove2.me/submissions/6d1e802b-1ecd-4308-a374-5af63b693e04

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_search
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_second_search
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_successful_nonzero_output


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroEmptySuffix
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) (ht : secondReadout S 0 u q≠0) :
    D S (secondReadout S 0 u q)≠0 :=
  BDL26LevelTwoLocalBranchEndpoint.successful_nonzero_output S _ (second_search S u q hs) ht
end QEC.Coding.BDL26FirstZeroEmptySuffix
