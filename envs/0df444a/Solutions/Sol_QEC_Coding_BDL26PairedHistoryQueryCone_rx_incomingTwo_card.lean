-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.rx_incomingTwo_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:27:20.902738+00:00
-- url     : https://prove2.me/submissions/4d0e6281-33a3-4f9d-8861-7d9876d979dc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_incomingTwo_subset
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_actual_inNeighbors_card_le
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_forwardTwo_card_le
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
    (xiIndexSet (rxData S depth i h).levelGraph.graph v 2).card ≤ 57 :=
  (Finset.card_le_card (incomingTwo_subset _ v)).trans
    (forwardTwo_card_le _ (actual_inNeighbors_card_le S depth i h) v)
end QEC.Coding.BDL26PairedHistoryQueryCone
