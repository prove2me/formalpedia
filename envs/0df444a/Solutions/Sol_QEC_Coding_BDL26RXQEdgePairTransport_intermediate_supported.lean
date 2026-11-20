-- Prove2me | solution 1 for QEC.Coding.BDL26RXQEdgePairTransport.intermediate_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:14:21.895277+00:00
-- url     : https://prove2.me/submissions/e848adf5-bf98-4aea-8323-9dee625c01d7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_localized_support_cast
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_computed_parent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_rx


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
    (j : Nat) (hN : 2*j+3≤N) (a : Seed S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : w.word=canonicalBasisWord (F:=F) (seedPhysical S j a)) :
    hammingSupport (middle S N sigma tau j hN w).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (qEdgeOwner S j a.1 a.2.1) := by
  have hp := computed_parent S N sigma tau j hN a w hw
  have hs0 := (step S N sigma tau (rxIndex N j hN) w).lower.supported
  rw [step_rx S N sigma tau (rxIndex N j hN) (rx_even N j hN) w] at hs0
  change hammingSupport (BDL26RXPhysicalStarTransport.L S (N+2)
    (Edge N (rxIndex N j hN)) (rx_even N j hN) w.center _ _) ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (BDL26RXPhysicalStarTransport.parentX S (N+2)
          (Edge N (rxIndex N j hN)) (rx_even N j hN) w.center) at hs0
  rw [hp] at hs0
  have hs : hammingSupport (step S N sigma tau (rxIndex N j hN) w).lower.word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (qEdgeOwner S j a.1 a.2.1) := by
    rw [step_rx S N sigma tau (rxIndex N j hN) (rx_even N j hN) w]
    exact hs0
  have heq : hammingSupport (middle S N sigma tau j hN w).word=
      hammingSupport (step S N sigma tau (rxIndex N j hN) w).lower.word :=
    eq_of_heq (localized_support_cast (index_pair N j hN)
      (step S N sigma tau (rxIndex N j hN) w).lower)
  intro r hr
  exact hs (Eq.mp (congrArg (fun a : Finset (Physical S (2*j+4)) => r∈a) heq) hr)
end QEC.Coding.BDL26RXQEdgePairTransport
