-- Prove2me | solution 1 for QEC.Coding.BDL26HigherRXFaceTower.seed_window_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:23:24.726343+00:00
-- url     : https://prove2.me/submissions/96fed517-0e67-4388-bc4e-87c4fa4f0d26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_adjacent_potential_pair


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HigherRXFaceTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators
namespace QEC.Coding.BDL26HigherRXFaceTower
theorem _root_.solution (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (j : Nat) (hN : 2*j+3 ≤ N) :
    intervalPotential S N sigma tau top (rzIndex N j hN).castSucc (rxIndex N j hN).succ=
      edgePotential S N sigma tau top (rxIndex N j hN)+
        ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
          ((seed_indices N j hN).2.2 ▸ edgePotential S N sigma tau top (rzIndex N j hN)) :=
  adjacent_potential_pair S N sigma tau top _ _ (seed_indices N j hN).2.2
end QEC.Coding.BDL26HigherRXFaceTower
