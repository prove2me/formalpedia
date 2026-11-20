-- Prove2me | solution 1 for QEC.Coding.BDL26RXQEdgePairTransport.window_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:27:25.622968+00:00
-- url     : https://prove2.me/submissions/2daa305f-d75b-4c02-8e37-27fb7338d7ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_adjacent_potential_pair
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    intervalPotential S N sigma tau top (rzIndex N j hN).castSucc (rxIndex N j hN).succ=
      edgePotential S N sigma tau top (rxIndex N j hN)+
        ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
          ((index_pair N j hN).symm ▸ edgePotential S N sigma tau top (rzIndex N j hN)) :=
  adjacent_potential_pair S N sigma tau top _ _ (index_pair N j hN).symm
end QEC.Coding.BDL26RXQEdgePairTransport
