-- Prove2me | solution 1 for QEC.Coding.BDL26RXQEdgePairTransport.window_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:32:17.12618+00:00
-- url     : https://prove2.me/submissions/fa8ba862-5f27-4a11-a106-e5b0ce631d54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_interior_pair_equation
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
    intervalMap1 (SuffixData S N) (rzIndex N j hN).castSucc (rxIndex N j hN).succ
      (by change 2*j+1≤2*j+3; omega)
      (path S N sigma tau top (rzIndex N j hN).castSucc).word=
      (path S N sigma tau top (rxIndex N j hN).succ).word+
        correctionIntervalSum S N sigma (rzIndex N j hN).castSucc (rxIndex N j hN).succ+
        correctionIntervalSum S N tau (rzIndex N j hN).castSucc (rxIndex N j hN).succ+
        (SuffixData S N).family.coboundary0 (rxIndex N j hN).succ
          (edgePotential S N sigma tau top (rxIndex N j hN)+
            ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
              ((index_pair N j hN).symm ▸ edgePotential S N sigma tau top (rzIndex N j hN))) :=
  interior_pair_equation S N sigma tau top _ _ (index_pair N j hN).symm
end QEC.Coding.BDL26RXQEdgePairTransport
