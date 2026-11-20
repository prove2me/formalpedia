-- Prove2me | solution 1 for QEC.Coding.BDL26HigherRXFaceTower.seed_window_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:23:28.015039+00:00
-- url     : https://prove2.me/submissions/1ebbd8db-ee25-4547-a965-964188c4dc85

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_interior_pair_equation


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
    intervalMap1 (SuffixData S N) (rzIndex N j hN).castSucc (rxIndex N j hN).succ
      (by change 2*j+1 ≤ 2*j+3; omega)
      (path S N sigma tau top (rzIndex N j hN).castSucc).word=
      (path S N sigma tau top (rxIndex N j hN).succ).word+
        correctionIntervalSum S N sigma (rzIndex N j hN).castSucc (rxIndex N j hN).succ+
        correctionIntervalSum S N tau (rzIndex N j hN).castSucc (rxIndex N j hN).succ+
        (SuffixData S N).family.coboundary0 (rxIndex N j hN).succ
          (edgePotential S N sigma tau top (rxIndex N j hN)+
            ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
              ((seed_indices N j hN).2.2 ▸ edgePotential S N sigma tau top (rzIndex N j hN))) :=
  interior_pair_equation S N sigma tau top _ _ (seed_indices N j hN).2.2
end QEC.Coding.BDL26HigherRXFaceTower
