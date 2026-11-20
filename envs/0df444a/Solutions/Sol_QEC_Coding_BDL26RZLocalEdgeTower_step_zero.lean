-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalEdgeTower.step_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:21:12.937745+00:00
-- url     : https://prove2.me/submissions/96e429f4-6bce-4f7e-bfe4-8c700fad0165

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_rx
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_rz
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_self
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_self
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_lowerError_coordinates
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.lower_self
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.lower_self



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RZLocalEdgeTower
theorem _root_.solution (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (w : LocalizedWord S n sigma tau i.succ) (hw : w.word=0) :
    (step S n sigma tau i w).lower.word=0 := by
  by_cases he : (BDL26LocalizedHistoryErrorDescent.Edge n i).val%2=0
  · have hs : second S n sigma tau i w=first S n sigma i := by
      change first S n sigma i+w.word=first S n sigma i
      rw [hw,add_zero]
    rw [step_rx S n sigma tau i he w]
    change BDL26RXPhysicalStarTransport.L S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) he w.center
      (first S n sigma i) (second S n sigma tau i w)=0
    rw [hs]
    exact BDL26RXPhysicalStarTransport.lower_self S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) he w.center _
  · rw [step_rz S n sigma tau i he w]
    change BDL26RZFiniteBlockTransport.lowerError S (n+2) (BDL26LocalizedHistoryErrorDescent.Edge n i) he
      (first S n sigma i) (second S n sigma tau i w)=0
    rw [BDL26RZFiniteBlockTransport.lowerError_coordinates,representatives_difference,hw,map_zero,map_zero]
end QEC.Coding.BDL26RZLocalEdgeTower
