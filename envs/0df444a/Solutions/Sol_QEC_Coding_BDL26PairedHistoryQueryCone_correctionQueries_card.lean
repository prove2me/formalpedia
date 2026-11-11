-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.correctionQueries_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:43:44.577778+00:00
-- url     : https://prove2.me/submissions/0b91db1c-f9c5-40e4-9eec-0879b3100f99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_ownerRead_card
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_affected_card
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
theorem _root_.solution (U : Finset (FamilyZ S depth i.succ)) :
    (correctionQueries S depth i U).card ≤ queryBlockBound S * (57 * U.card) := by
  exact (Finset.card_biUnion_le_card_mul _ _ (queryBlockBound S)
    (fun v _ => ownerRead_card S depth i v)).trans
      (by have h := affected_card S depth i U; nlinarith)
end QEC.Coding.BDL26PairedHistoryQueryCone
