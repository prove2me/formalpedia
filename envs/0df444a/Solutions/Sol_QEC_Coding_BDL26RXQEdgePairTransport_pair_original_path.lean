-- Prove2me | solution 1 for QEC.Coding.BDL26RXQEdgePairTransport.pair_original_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:51:34.032696+00:00
-- url     : https://prove2.me/submissions/52b08d4d-f96d-4555-b762-37952547768b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_path_cast
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_step


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQEdgePairTransport
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalizedHistoryErrorDescent BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26OwnerIncidenceMasks BDL26HistoryLogicalResidual BDL26TannerLocalRegularity
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXQEdgePairTransport
theorem _root_.solution (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (j : Nat) (hN : 2*j+3≤N) :
    (pairResult S N sigma tau j hN (path S N sigma tau top (rxIndex N j hN).succ)).lower=
      path S N sigma tau top (rzIndex N j hN).castSucc := by
  unfold pairResult middle
  have hmiddle : cast (congrArg (LocalizedWord S N sigma tau) (index_pair N j hN))
      (step S N sigma tau (rxIndex N j hN)
        (path S N sigma tau top (rxIndex N j hN).succ)).lower=
      path S N sigma tau top (rzIndex N j hN).succ := by
    rw [← path_step]
    exact path_cast S N sigma tau top (index_pair N j hN)
  rw [hmiddle,← path_step]
end QEC.Coding.BDL26RXQEdgePairTransport
