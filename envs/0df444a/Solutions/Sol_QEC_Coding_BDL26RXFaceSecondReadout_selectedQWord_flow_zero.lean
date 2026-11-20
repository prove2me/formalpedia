-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_flow_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:13:09.472027+00:00
-- url     : https://prove2.me/submissions/e6e772e9-4bd8-4b47-ba44-2aff9118c1ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cqComponentTotal_local_flow_weight


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
theorem _root_.solution (sigma : Syn) (q : P.Q)
    (hq : restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)=0) :
    BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)=0 := by
  have hrange : RXCoarseGraining.RXCoarseGrainingData.CqLocalRangeAt Data sigma.val q := by
    change restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)∈_
    rw [hq]
    exact ⟨0,map_zero _⟩
  apply (HammingWeight_eq_zero_iff _).mp
  have hw := RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal_local_flow_weight Data sigma.val q hrange
  change HammingWeight (BDL26RXDecoderAdapter.qFlow P witnessScale q
    (selectedQWord sigma q)) ≤ _ at hw
  rw [hq,HammingWeight_zero] at hw
  exact Nat.le_zero.mp hw
end QEC.Coding.BDL26RXFaceSecondReadout
