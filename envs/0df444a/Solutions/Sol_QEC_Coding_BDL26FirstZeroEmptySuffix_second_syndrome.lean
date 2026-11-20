-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.second_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:55:32.136315+00:00
-- url     : https://prove2.me/submissions/0b2793a0-d3b8-414a-920d-9b0224408dff

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_empty_descent
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_terminal_syndrome
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (hs : firstReadout S 0 u=0) :
    delta S (flip S 0 q)=secondReadout S 0 u q := by
  have hword : (descent S 0 u q).word=(flip S 0 q : Error S) :=
    (empty_descent S u q).1
  exact (congrArg (delta S) hword).symm.trans
    (BDL26FirstZeroFaceEndpoint.terminal_syndrome S 0 u q hs)
end QEC.Coding.BDL26FirstZeroEmptySuffix
