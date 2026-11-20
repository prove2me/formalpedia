-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_boundary_old_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:13:12.906172+00:00
-- url     : https://prove2.me/submissions/6d37a5e7-e12f-4a30-bf77-5909d13ccc42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_q_component_boundary
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
noncomputable section
namespace QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators
private theorem old_z_not_q_region (T : TannerSquarePresentation) (S : OddScale)
    (q : T.Q) (z : T.Z) (c : BDL26FiniteTannerSquare.Two) :
    Sum.inr (z,c)∉(localQ T S).syndromeRegion q := by
  intro hz
  have he := (Finset.mem_filter.mp hz).2
  change (Vertex.z z : Vertex T)=Vertex.q q at he
  cases he
end QEC.Coding.BDL26RXFaceSecondReadout
end
end

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
theorem _root_.solution (sigma : Syn) (q : P.Q) (z : P.Z) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q) (Sum.inr (z,c))=
      BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)
        (Sum.inr (z,c)) := by
  let f := restrictWordLinear (Lq.correctionRegion q)
    (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)
  have hb : (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q)=
      (fun p : RX2 P witnessScale => extendWordLinear (Lq.syndromeRegion q)
        (Data.contract.rx_local_complexes.cqDelta1 q f) p+
        BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q) p) :=
    q_component_boundary witnessScale 3 rxIndex rxIndex_even sigma.val q
  have he := congrArg (fun w : Word F (RX2 P witnessScale) => w (Sum.inr (z,c))) hb
  have hout : Sum.inr (z,c)∉Lq.syndromeRegion q := by
    change Sum.inr (z,c)∉(localQ P witnessScale).syndromeRegion q
    exact old_z_not_q_region P witnessScale q z c
  have hz : extendWordLinear (Lq.syndromeRegion q)
      (Data.contract.rx_local_complexes.cqDelta1 q f) (Sum.inr (z,c))=0 :=
    dif_neg hout
  exact he.trans (by rw [hz,zero_add])
end QEC.Coding.BDL26RXFaceSecondReadout
