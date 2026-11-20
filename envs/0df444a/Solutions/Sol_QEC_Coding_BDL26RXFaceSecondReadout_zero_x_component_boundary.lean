-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.zero_x_component_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:11:24.996859+00:00
-- url     : https://prove2.me/submissions/fbaa7b9c-9d66-43e0-9796-971ecce94ba6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_x_component_boundary
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cxComponentTotal_local_delta
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cxComponentTotal_local_flow_weight
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (sigma : Syn) (x : P.X)
    (hx : restrictWordLinear (Lx.syndromeRegion x) sigma.val=0) :
    (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)=0 := by
  have hrange : RXCoarseGraining.RXCoarseGrainingData.CxLocalRangeAt Data sigma.val x := by
    change restrictWordLinear (Lx.syndromeRegion x) sigma.val∈_
    rw [hx]
    exact ⟨0,map_zero _⟩
  let f := restrictWordLinear (Lx.correctionRegion x)
    (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)
  have hlocal : Data.contract.rx_local_complexes.cxDelta1 x f=0 :=
    (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal_local_delta Data sigma.val x hrange).trans hx
  have hflow : Data.contract.support_decomposition.cxFlow x f=0 := by
    apply (HammingWeight_eq_zero_iff _).mp
    have hw := RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal_local_flow_weight Data sigma.val x hrange
    rw [hx,HammingWeight_zero] at hw
    exact Nat.le_zero.mp hw
  have hb : (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)=
      (fun p : RX2 P witnessScale => extendWordLinear (Lx.syndromeRegion x)
        (Data.contract.rx_local_complexes.cxDelta1 x f) p+
        Data.contract.support_decomposition.cxFlow x f p) :=
    x_component_boundary witnessScale 3 rxIndex rxIndex_even sigma.val x
  exact hb.trans (by
    funext p
    rw [hlocal,hflow,map_zero]
    change (0:F)+0=0
    exact add_zero 0)
end QEC.Coding.BDL26RXFaceSecondReadout
