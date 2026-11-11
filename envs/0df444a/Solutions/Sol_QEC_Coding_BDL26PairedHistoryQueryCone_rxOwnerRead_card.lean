-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.rxOwnerRead_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:31:10.399125+00:00
-- url     : https://prove2.me/submissions/6a65e593-9877-4fcf-8db9-5c3875ec988f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_rx_incomingTwo_card
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_rx_region_card
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (h : i.val % 2 = 0) (v : Owners S depth i) :
    (rxOwnerRead S depth i h v).card ≤ queryBlockBound S := by
  have hb := Finset.card_biUnion_le_card_mul
    (xiIndexSet (rxData S depth i h).levelGraph.graph v 2)
    (fun w => (rxXiLocalComplex (rxData S depth i h)).syndromeRegion w)
    (localCoordinateBound S) (fun w _ => rx_region_card S depth i h w)
  exact hb.trans (Nat.mul_le_mul_right _ (rx_incomingTwo_card S depth i h v))
end QEC.Coding.BDL26PairedHistoryQueryCone
