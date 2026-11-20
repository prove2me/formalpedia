-- Prove2me | solution 1 for QEC.Coding.BDL26RXQEdgePairTransport.pair_original_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:32:10.532227+00:00
-- url     : https://prove2.me/submissions/cbe81188-c60a-42a3-b9bb-25aa815013ce

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport

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
    (j : Nat) (hN : 2*j+3≤N)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ) :
    (pairResult S N sigma tau j hN w).lower=
      (step S N sigma tau (rzIndex N j hN)
        (step S N sigma tau (rxIndex N j hN) w).lower).lower := by
  unfold pairResult
  have hm : middle S N sigma tau j hN w=
      (show LocalizedWord S N sigma tau (rzIndex N j hN).succ from
        (step S N sigma tau (rxIndex N j hN) w).lower) :=
    eq_of_heq (cast_heq _ _)
  rw [hm]
end QEC.Coding.BDL26RXQEdgePairTransport
