-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.zero_x_cleaned_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:28:27.377506+00:00
-- url     : https://prove2.me/submissions/87c24d91-7c53-4033-8671-b32edaa4a5df

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_zero_x_component_boundary

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXFaceSecondReadout
theorem _root_.solution (sigma : Syn)
    (hx : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma.val=0) :
    RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val=sigma.val := by
  have hc : (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cxCorrectionTotal Data sigma.val)=0 := by
    change (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (∑ x,RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)=0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun x _ => zero_x_component_boundary sigma x (hx x))
  change sigma.val+(indexedFamily witnessScale 3).coboundary1 rxIndex.succ
    (RXCoarseGraining.RXCoarseGrainingData.cxCorrectionTotal Data sigma.val)=sigma.val
  rw [hc,add_zero]
end QEC.Coding.BDL26RXFaceSecondReadout
